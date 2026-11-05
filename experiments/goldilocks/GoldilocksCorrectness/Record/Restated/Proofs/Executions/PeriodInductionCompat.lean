module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteHeadKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26Held
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodRevocation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFinalityChainBlock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodJustifiedPast
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78Compat
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodCompatCopies
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Proofs.Executions.Lemma26Held
public import GoldilocksCorrectness.Proofs.Executions.PeriodRevocation
public import GoldilocksCorrectness.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Proofs.Executions.PeriodFinalityChainBlock
public import GoldilocksCorrectness.Proofs.Executions.PeriodJustifiedPast
public import GoldilocksCorrectness.Proofs.Executions.Lemma78Compat
public import GoldilocksCorrectness.Proofs.Executions.PeriodCompatCopies
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodInductionCompat, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodInductionCompat.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the asynchronous period under
the compatible vote clause, namely the voters of a slot whose votes are compatible with `B` and
their majority of the committee, no honest confirmation of a timely slot conflicting with `B`, an
honest active vote at a timely slot on `B`'s chain or compatible with `B` from a voter justified
past `B`, the joint induction `PeriodInvCompatDueByCutoff` at every step after the hand-over update,
Lemma 104 with the compatible vote clause, and its two corollaries. The page's routine-level
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
  one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem slot_of_update_after_deadline
  supportCutoff_cast supportCutoff_eq supportCutoff_slot supportCutoff_slot_eq viewFreeze_cast
  viewFreeze_eq voteTime_eq voteTime_mono' voteTime_succ' votes_due_of_after_period)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith HeadOf)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The voters of a slot whose votes are compatible with `B` -/

/-- The members of a set `Q` of honest active committee members of slot `σ`, each of whose
slot-`σ` votes is for a block it holds compatible with `B`, have such a vote: a block `H u` for
each, `u`'s slot-`σ` vote for `H u` is on the wire at its tick at the vote time of `σ`, `u` holds
`H u` then, `H u` is compatible with `B`, and `u` is a committee member honest at the support
cutoff of slot `σ + 1`. The copy of `exists_votes_on_chain` with "compatible with `B`" in place
of "`B` or a descendant of `B`".

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot; `Q`: the voters;
  `B`: the block.

Read aloud: every honest active committee member of slot `σ` whose slot-`σ` votes are compatible
with `B` has such a vote, for a block it holds that is compatible with `B`. -/
theorem exists_votes_compatible (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (σ : ℕ) (Q : Finset V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hQ : Q ⊆ honestActiveAt M S A x σ ∩ S.P.committee σ)
    (hExt : ∀ u ∈ Q, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
        vote = GoldfishVote.mk u σ H_u.root ∧ H_u.compatible B = true) :
    ∃ H : V → Block V, ∀ u ∈ Q, u ∈ S.P.committee σ ∧
      u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C σ)).tree ∧ (H u).compatible B = true := by
  classical
  have key : ∀ u ∈ Q, ∃ Hu : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ Hu.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      Hu ∈ (x.tickInput u (M.voteTime S.C σ)).tree ∧ Hu.compatible B = true := by
    intro u hu
    obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.honest_active_votes M F U) S A x R σ u E hSkew hA hK
    obtain ⟨Hu, hHuT, hveq, hBH⟩ := hExt u hu vote ⟨i, hl, hsent⟩
    exact ⟨Hu, ⟨i, hl, hveq ▸ hsent⟩, hHuT, hBH⟩
  refine ⟨fun u => if h : u ∈ Q then Classical.choose (key u h) else B, fun u hu => ?_⟩
  obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
  have hspec := Classical.choose_spec (key u hu)
  simp only [dif_pos hu]
  exact ⟨hK, fun h => (Finset.mem_sdiff.1 hA).2 (Finset.mem_union_left _ h), hspec⟩

/-- The voters of slot `s'` whose votes `VotesCompatibleAt` makes compatible with `B` outweigh the
rest of the committee: the lock holders' members of the committee when the previous votes were
owed inside the period (`P.hHold`; their conjunct is read at `s' ≤ s + k`, `owed_slot_le_k`), and
the honest active members otherwise (`P.hSleepK`). The copy of `voters_on_chain_majority`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s' + 1` is at most `T`, so the committee of `s'` is
  among those `P.hSleepK` covers.

Read aloud: the voters of slot `s'` whose votes are compatible with `B` outweigh the rest of its
committee. -/
theorem voters_compatible_majority (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
      (s' : ℕ)
    -- the committee of slot `s'` is among those `P` counts
    (hT : M.supportCutoff S.C (s' + 1) ≤ T)
    (hs' : s + 1 ≤ s') (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    ∃ Q : Finset V, Q ⊆ honestActiveAt M S A x s' ∩ S.P.committee s' ∧
      (∀ u ∈ Q, ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i) →
        ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
          vote = GoldfishVote.mk u s' H_u.root ∧ H_u.compatible B = true) ∧
      (S.P.committee s' \ Q).card < Q.card := by
  classical
  by_cases hOwed : VotesOwedInPeriod M S Δs b₀ b₁ s'
  · have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 : s' - 1 ≤ s + 1 := by omega
      have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' - 1)
      have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
      have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S h1
      have h5 := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold s' hs2 hOwed.1 hOwed.2
    refine ⟨holdersAt M S A x s s' ∩ S.P.committee s', ?_,
      fun u hu => (holders_vote_compatible_of_votesCompatibleAt M F) hVotes
        ((owed_slot_le_k M F U) P.hb₁ hOwed) u (Finset.mem_inter.1 hu).1, ?_⟩
    · intro u hu
      simp only [holdersAt, Finset.mem_inter] at hu ⊢
      exact ⟨hu.1.2, hu.2⟩
    · have heq : S.P.committee s' \ (holdersAt M S A x s s' ∩ S.P.committee s') =
          S.P.committee s' \ holdersAt M S A x s s' := by
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [heq]
      exact hlt
  · refine ⟨honestActiveAt M S A x s' ∩ S.P.committee s', subset_rfl,
      fun u hu => (active_vote_compatible_of_votesCompatibleAt M F) hVotes hOwed u
        (Finset.mem_inter.1 hu).1, ?_⟩
    have hanchor : anchor ≤ M.slotStart S.C (s' + 1) :=
      le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    have hK := P.hSleepK (s' + 1) (by omega) hanchor hT
    rw [Nat.add_sub_cancel] at hK
    have hsub : S.P.committee s' \ (honestActiveAt M S A x s' ∩ S.P.committee s') ⊆
        S.P.committee s' \ honestActiveAt M S A x s' := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
      tauto
    exact lt_of_le_of_lt (Finset.card_le_card hsub) hK

/-- After a period that ends, with its recovery `max (Δ S) Δs`, before the vote time of slot `s + k`, the
period plus its recovery ends by the support cutoff of every slot `s' ≥ s + k`: the second disjunct of
`VotesDueByCutoff`. A proof-page helper.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the hand-over slot; `s'`: the slot; `b₁`: the period's end; `Δs`: the sync
  delay.

Read aloud: the votes of every slot from `s + k` on are due after the period and its recovery. -/
theorem votes_due_of_after_period_max (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {s s' b₁ Δs : ℕ} (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)) (hs' : s + S.C.k ≤ s') :
    b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C s' := by
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S hs'
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
  omega

/-!-/

/-- **A member of `A.activeThroughoutToTick x a b` ticks to `b`, honest at that tick.**

Why: some step `k'` is `v`'s tick to `b` and `v` is active (awake and outside the adversary set)
after it (`mem_activeThroughoutToTick`); `x.tickStep` names that step (`tickStep_eq_of_lbl`).

The variables:
- `M`: the model; `F`: its facts; `E`: the environment's facts; `hv`: `v` is awake and honest up to
  its tick to `b`, from `a` or from the start.

Read aloud: a validator active up to its tick to `b` ticks to `b` and is honest at that tick. -/
theorem tick_honest_of_activeThroughoutToTick {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a : ℤ} {b : ℕ} {v : V} (hv : v ∈ A.activeThroughoutToTick x a b) :
    x.lbl (x.tickStep v b) = Event.tick v b ∧ v ∉ A.corrupted (x.tickStep v b) := by
  obtain ⟨k', hk', h | ⟨k, hkk, c, -, -, h⟩⟩ :=
    GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_activeThroughoutToTick.1 hv
  · rw [E.tickStep_eq_of_lbl hk']
    exact ⟨hk', (GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_active.1 (h k' le_rfl)).2⟩
  · rw [E.tickStep_eq_of_lbl hk']
    exact ⟨hk', (GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_active.1 (h k' hkk le_rfl)).2⟩

/-- **An honest active validator of slot `s` is honest at the tick to the support cutoff of slot
`s + 1` of any validator active up to that tick.**

Why: that validator is honest at its tick (`tick_honest_of_activeThroughoutToTick`), and
`honestActiveAt` excludes every validator in the adversary set at an honest validator's tick to that
cutoff.

The variables:
- `M`: the model; `F`: its facts; `E`: the environment's facts; `hu`: `u` is an honest active
  validator of slot `s`; `hv`: `v` is active up to its tick to the support cutoff of slot `s + 1`.

Read aloud: an honest active validator of slot `s` is honest when an honest validator counts the
slot's votes. -/
theorem not_mem_corrupted_tickStep_of_honestActiveAt {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {a : ℤ} {u v : V} (hu : u ∈ honestActiveAt M S A x s)
    (hv : v ∈ A.activeThroughoutToTick x a (M.supportCutoff S.C (s + 1))) :
    u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) := by
  obtain ⟨hl, hvh⟩ := (tick_honest_of_activeThroughoutToTick M F) E hv
  intro hc
  have h2 := (Finset.mem_sdiff.1 hu).2
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h2
  exact h2.2 ⟨_, v, hl, hvh, hc⟩

omit [RootOrder] in
/-- **After the period `[b₀, b₁)`, the suspended sync fact gives the sync fact from `max b₁ GST`
on**, at the same sync delay `Δs`: the suspended deadline is at most `Δs` after the later of the
time and `max b₁ GST` (`deadlineOutside_le_after`), and a promise by earlier deadlines gives the
promise by later ones (`SyncedWithinBy.of_le`).

The variables:
- `M`: the model; `F`: its facts; `Sy`: the sync fact suspended on `[b₀, b₁)`.

Read aloud: once the period is over, what an honest active validator would serve spreads within `Δs`
from `max b₁ GST` on. -/
theorem syncedWithin_after_period_of_outside {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {serves : M.N → ℕ → NamedObject V → Prop} {ok : NamedObject V → Prop}
    {release : NamedObject V → Option ℕ} {ΔRedeliver Δs GST b₀ b₁ : ℕ}
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinOutside A x serves ok release ΔRedeliver Δs GST b₀ b₁) :
    GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithin A x serves ok release ΔRedeliver Δs (max b₁ GST) :=
  GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy.of_le (fun _ _ t d' h => ⟨_, rfl, by
    have h' : max t (max b₁ GST) + Δs = d' := Option.some.inj h
    rw [← h']
    exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutside_le_after Δs GST b₀ b₁ t⟩) Sy

omit [RootOrder] in
/-- **The duty window's start is monotone in the slot**: `duty_window_start S.C s = S.C.t_ s + Δ − 4Δk`
(`duty_window_start_eq`) and the slot start is monotone (`slotStart_mono`, through `slotStart_cast`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `h`: `s ≤ s'`.

Read aloud: a later slot's duty window starts no earlier. -/
theorem duty_window_start_le_of_le (U : UniformSchedule M.toSlotLayout) (S : Setup V) {s s' : ℕ}
    (h : s ≤ s') : duty_window_start S.C s ≤ duty_window_start S.C s' := by
  rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq, GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq,
    ← (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s,
    ← (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s']
  have h1 : ((M.slotStart S.C s : ℕ) : Int) ≤ M.slotStart S.C s' := by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  linarith

/-! ## Statement 2′: the confirmations of a slot whose votes are due by its support cutoff -/

/-- **Statement 2′: no confirmation of a timely slot conflicts with `B`.** The proof; the audited
statement is in `Statements/Executions/PeriodInductionCompatStatements.lean`. Statement 2's proof
(`confirmation_extends_B_of_timely_votes`) with Lemma 78c and its twin in place of Lemma 78 and its
twin, and `voters_compatible_majority` in place of `voters_on_chain_majority`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot; `v`: the validator whose update it is.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s' + 1` is at most `T`, so the committee of `s'` is
  among those `P.hSleepK` covers.

Roots name blocks until `M.supportCutoff S.C s'`: Lemma 78c (or its twin) at slot `s'`.

Read aloud: once the votes of a slot are due by its support cutoff, no honest confirmation of that
slot conflicts with `B`. -/
theorem confirmation_compatible_of_timely_votes (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (v : V)
    -- the committee of slot `s'` is among those `P` counts
    (hT : M.supportCutoff S.C (s' + 1) ≤ T)
    -- roots name blocks among what honest validators hold up to the real time of `v`'s own tick to the support
    -- cutoff of `s'`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s'))))
    (hs' : s + 1 ≤ s') (hgood : VotesDueByCutoff M S Δs b₀ b₁ s')
    (hv : v ∈ honestActiveAt M S A x s')
    (hF : (x.tickInput v (M.supportCutoff S.C (s' + 1))).finalized.compatible B = true)
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C'.compatible B = true := by
  obtain ⟨Q, hQsub, hQext, hQcard⟩ := (voters_compatible_majority M F U) P s' hT hs' hVotes
  obtain ⟨Hf, hHs₀⟩ := (exists_votes_compatible M F U) S A x R s' Q B E hSkew hQsub hQext
  -- the voters are honest at `v`'s tick to the support cutoff of `s' + 1`
  have hHs : ∀ u ∈ Q, u ∈ S.P.committee s' ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s' + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' (Hf u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      Hf u ∈ (x.tickInput u (M.voteTime S.C s')).tree ∧ (Hf u).compatible B = true := fun u hu =>
    ⟨(hHs₀ u hu).1, (not_mem_corrupted_tickStep_of_honestActiveAt M F) E (Finset.mem_inter.1 (hQsub hu)).1
      ((honestActiveAt_window M F) S A s' v E hv),
      (hHs₀ u hu).2.2⟩
  have hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') <
      2 * Q.card :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v s') hQcard
  have hv' : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.supportCutoff S.C (s' + 1)) :=
    GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_activeThroughoutToTick_of_le
      ((duty_window_start_le_of_le M F U) S (Nat.le_succ s'))
      ((honestActiveAt_window M F) S A s' v E hv)
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s' := le_trans P.hGST
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  -- every voter is active through the sync fact's window at slot `s'`: its duty window
  -- (`honestActiveAt_window`) holds the window (`holder_window_of_updater_reader`)
  have hHold : ∀ u ∈ Q, u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun u hu =>
    (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGSTs
      (GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_activeThroughoutToTick_of_le
        ((duty_window_start_le_of_le M F U) S (Nat.le_succ s'))
        ((honestActiveAt_window M F) S A s' u E (Finset.mem_inter.1 (hQsub hu)).1))
  rcases hgood with hA | hB
  · -- before the period: the bounded delivery promise and the sync fact up to `b₀`
    exact (lem78c_update_confirmation_compatible_of_voter_majority_upTo M F U)
      S A x R GST s' Q Hf B v
      ((envFactsBy_of_synchronyFromWakeUpTo M) x E (((synchronyFromWakeUpTo_of_outside M) P.hSync).mono M hA))
      hNet hSkew hRedeliver (P.Sy.upTo.mono hA) hΔs
      hRoots P.hParent (votesCastByOwner_of_unforgeability M F S A x R E) hGSTs hHs hHold hVoters hv' hF
  · -- after the period plus its recovery: the synchronous promise and the sync fact from `max b₁ GST`
    exact (lem78c_update_confirmation_compatible_of_voter_majority M F U)
      S A x R (max b₁ GST) s' Q Hf B v
      ((envFactsBy_of_synchronyFromWakeBy M) x E ((synchronyFromWake_of_outside_after M) P.hSync))
      hNet hSkew hRedeliver ((syncedWithin_after_period_of_outside M F) P.Sy) hΔs
      hRoots P.hParent (votesCastByOwner_of_unforgeability M F S A x R E) (by omega) hHs hHold hVoters hv' hF

/-! ## Statement 1′: the votes of a timely slot -/

/-- **After the revocation against a delivered majority on `B`'s chain, no lock entry conflicts with `B`, read at
`u`'s tick input to the vote time of slot `σ + 1`.** `revoked_entries_compatible_of_majority` with the revocation's
answer read from `u`'s tick input (rule R3) in place of its state before the vote time.

Why: every voter of `Hs` has its slot-`σ` vote held by `u` as its only slot-`σ` vote, so no voter of `Hs` is an
equivocator, and its vote resolves for a block conflicting with the block of a lock entry that conflicts with `B`;
the revocation keeps an entry only when its opponents weigh less than half the committee
(`revoke_locks_entry_opponents_lt`), and `Hs` is more than half of it.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
  `σ`: the slot of the votes; `tb`: the bound on their stamps; `u`: the revoking validator; `Hs`: the voters; `H`:
  the block each voter's vote is for; `B`: the block.

Read aloud: after the revocation at `u`'s tick against a delivered majority on `B`'s chain, no live lock conflicts
with `B`. -/
theorem revoked_entries_compatible_of_majority_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (σ tb : ℕ) (u : V) (Hs : Finset V) (H : V → Block V) (B : Block V)
    (hcard : |S.P.committee σ| < 2 * |Hs|)
    (hHB : ∀ u' ∈ Hs, B.AncestorEq (H u'))
    (hHeld : ∀ u' ∈ Hs, HeldEarlyVoteAt M (x.tickInput u (M.voteTime S.C (σ + 1)))
        ((tb : ℕ) : Int) σ (H u') u') :
    ∀ n' : M.N, GoldilocksCorrectness.Record.Statements.Routines.LocksRevoked M S.P
        (x.tickInput u (M.voteTime S.C (σ + 1))) ((M.voteTime S.C (σ + 1) : ℕ) : Int) (σ + 1) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput u (M.voteTime S.C (σ + 1)))
          ((M.voteTime S.C (σ + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro n' hRev e he _
  obtain ⟨opp, hopp, hlt⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_opponents_lt (s := σ + 1) (Nat.succ_ne_zero σ) hRev e he
  simp only [Nat.add_sub_cancel] at hopp hlt
  by_contra hc
  -- every voter of `Hs` opposes `e.B`
  have hsub : Hs ⊆ opp := by
    intro u' hu'
    obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u' hu'
    -- the vote's voter is no equivocator: its one vote of slot `σ` is the only one `u` holds
    have hneq : u' ∉ M.equivocators (M.votesHeldSet (x.tickInput u (M.voteTime S.C (σ + 1))) σ) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_equivocators_iff_two M F)]
      rintro ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩
      exact hne ((huniq v₁ hv₁ h1).trans (huniq v₂ hv₂ h2).symm)
    -- the vote's block conflicts with `e.B`
    have hconf : (H u').conflicts e.B = true := by
      rw [GoldilocksCorrectness.Proofs.Routines.conflicts_iff, GoldilocksCorrectness.Proofs.Routines.compatible_iff]
      rintro (h | h)
      · exact hc ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2
          (Or.inr (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans (hHB u' hu') h)))
      · exact hc ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2
          (GoldilocksCorrectness.Proofs.Routines.ancestorEq_compatible h (hHB u' hu')))
    -- the vote resolves and opposes `e.B`: `u'` is among the opponents
    exact (hopp u').2 ⟨hneq, _, hp, rfl, ⟨y, hy⟩, ⟨H u', hHΦ, rfl, hconf⟩⟩
  have hle := Finset.card_le_card hsub
  omega

/-! ## Two of a validator's ticks, ordered; its clock value at the earlier one -/

/-- **Two ticks of one validator to clock values whose windows do not overlap are ordered as the
values are.** A tick to a clock value `d` is at a real time at most `ΔClockBehind` after `d`, and a tick
to `d'` at a real time at least `ΔClockAhead` before `d'`; when the first bound is less than the second,
the first tick's step is before the second's (real time is monotone along the steps).

The variables:
- `M`: the model; `F`: its facts; `x`: the execution; `R`, `E`: the run's facts and the environment's
  facts; `d`, `d'`: the two clock values; `u`: the validator.

Read aloud: a validator's tick to an earlier clock value comes at an earlier step, when the two
values are further apart than the clock bounds. -/
theorem tickStep_lt_of_window_gap {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {d d' : ℕ} {u : V}
    (hdd : (d : ℝ) + ΔClockBehind < (d' : ℝ) - ΔClockAhead)
    (hk : ∃ i : ℕ, x.lbl i = Event.tick u d)
    (hk' : ∃ i : ℕ, x.lbl i = Event.tick u d') :
    x.tickStep u d < x.tickStep u d' := by
  have h1 := (E.time_tickStep hk).2
  have h2 := (E.time_tickStep hk').1
  by_contra hc
  have := R.time_mono (Nat.le_of_not_lt hc)
  linarith

/-- **An updater of slot `s'` ticks to the support cutoff of `s'` at a step before its tick to the support cutoff of
`s' + 1`.** Both ticks exist: the first by `updater_reader_gives_core_window`, the second by
`tick_honest_of_activeThroughoutToTick`; the two values are `4 * Δ S` apart, so `tickStep_lt_of_window_gap` with
`hSkew` orders them.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `x`: the execution; `R`, `E`: the run's facts and
  the environment's facts; `Δs`: the sync delay; `s'`: the slot; `v`: the updater.

Read aloud: an updater's tick to a slot's support cutoff comes at an earlier step than its tick to the next slot's. -/
theorem tickStep_cut_lt_succ_of_updater (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {s' : ℕ} {v : V}
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.supportCutoff S.C (s' + 1))) :
    x.tickStep v (M.supportCutoff S.C s') < x.tickStep v (M.supportCutoff S.C (s' + 1)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S s'
  have hcR : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s' : ℕ) + 4 * Δ S := by
    exact_mod_cast hc
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hv
  have hk1 := ((tick_honest_of_activeThroughoutToTick M F) E hv).1
  exact (tickStep_lt_of_window_gap M F) x R E (by rw [hcR]; linarith) ⟨kR, hkR⟩ ⟨_, hk1⟩

/-- **A validator's tick to the view freeze of `σ` is at a step before its tick to the vote time of
`σ + 1`.** `tickStep_lt_of_window_gap` at the two values, which are `2 * Δ S` apart under
`UniformSchedule`, with `hSkew`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `x`: the execution; `R`, `E`: the
  run's facts and the environment's facts; `σ`: the slot; `u`: the validator.

Read aloud: a validator ticks to the view freeze of a slot before it ticks to the next slot's vote
time. -/
theorem tickStep_viewFreeze_lt_tickStep_voteTime_succ (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {σ : ℕ} {u : V}
    (hSkew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ))
    (hk : ∃ i : ℕ, x.lbl i = Event.tick u (M.viewFreeze S.C σ))
    (hk' : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1))) :
    x.tickStep u (M.viewFreeze S.C σ) < x.tickStep u (M.voteTime S.C (σ + 1)) := by
  refine tickStep_lt_of_window_gap M F x R E ?_ hk hk'
  have hvf := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S σ
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have e1 : ((M.viewFreeze S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 3 * Δ S := by
    rw [hvf, hss]; push_cast; ring
  have e2 : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 5 * Δ S := by
    rw [hvt, hss]; push_cast; ring
  rw [e1, e2]
  linarith

/-- **The clock value at a validator's tick to `c` is less than `c`, for a validator counted active up to
its tick to a later `e`.** When `u` is active from `a` up to its tick to `e`, and the window of real times
of a tick to `c` lies after `a` and before the window of a tick to `e`, then `u` is active at every step
from `c − ΔClockAhead` to its tick to `c` (`tick_window_of_activeThroughoutToTick_int`), and its clock
value at that tick's step is less than `c` (`clockValue_lt_of_tick_of_active`).

The variables:
- `M`: the model; `F`: its facts; `x`: the execution; `R`, `E`: the run's facts and the environment's
  facts; `a`: the start of `u`'s window; `c`: the clock value of the tick; `e`: the clock value that
  ends `u`'s window; `u`: the validator.

Read aloud: a validator active through a window shows a clock value less than `c` when it starts its
tick to `c`. -/
theorem clockValue_lt_at_tickStep_of_activeThroughoutToTick {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a : ℤ} {c e : ℕ} {u : V}
    (hu : u ∈ A.activeThroughoutToTick x a e)
    (hc0 : 0 < c)
    (hlo : (a : ℝ) + ΔClockBehind < (c : ℝ) - ΔClockAhead)
    (hhi : (c : ℝ) + ΔClockBehind < (e : ℝ) - ΔClockAhead)
    (hk : ∃ i : ℕ, x.lbl i = Event.tick u c) :
    x.clockValue (x.tickStep u c) u < c := by
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hu (t₀ := (c : ℝ) - ΔClockAhead) hlo
  have hkRe : kR = x.tickStep u e := ((tickStep_eq_of_lbl M) x E hkR).symm
  have hlt : x.tickStep u c < x.tickStep u e := tickStep_lt_of_window_gap M F x R E hhi hk ⟨kR, hkR⟩
  exact clockValue_lt_of_tick_of_active M F E (x.lbl_tickStep hk) hc0
    (fun j hj hjk => hwin j hj (by omega))

/-- **Statement 1′'s core: the vote of a timely slot, given the previous votes on `B`'s chain
whenever the voter is not justified past `B` and its finalized block is `B` or an ancestor of
`B`.** Statement 1′'s proof with `hExt` in place of its hypotheses on the previous slot (`hCprev`,
`hVotes`), which statement 1′ turns into `hExt` (`justified_past_spreads`); the induction calls
this form at slot `s + 2`, where the previous votes are the hand-over facts' and no caches of the
previous slot's voters are at hand. Write `σ := s' − 1` and
`n_u := stateBefore M x (M.voteTime S.C s') u`.

- `h(B) + 1 ≤ n_u.justifiedHeight`: Lemma 14, then `vote_head_compatible_of_justified_past` (the
caches, `hTwo`, `h_j_lt_h_max`, Lemma 11's computed chain states): the second disjunct.
- `n_u.justifiedHeight ≤ h(B)` and `n_u.finalized` not an ancestor of `B`: `B` is an ancestor of it
(the caches are compatible with `B`), and `vote_head_descends_of_F`: the first disjunct.
- `n_u.justifiedHeight ≤ h(B)` and `n_u.finalized ⪯ B`: not contested (`hNC` and
`h_max_of_contested`). The votes of `σ` are on `B`'s chain (`hExt`). Then v3's route: the voters'
majority (`voters_on_chain_majority`), the votes held (the twin of Lemma 12 when
`M.supportCutoff S.C σ ≤ b₀`, Lemma 12 by a later delay at the window ending at `b₁ + max (Δ S) Δs` otherwise),
the locks (`revoked_entries_compatible_of_majority`), `hF2` from the caches, `hF3` from `B` itself
when `hMax M S.C n_u ≤ h(B) + 1` and from the certified entry at `hMax M S.C n_u − 1` (Lemma 67, K3,
`mem_voter_tree_st` at `u`'s tick inputs to the view freeze of `σ` and the vote time) otherwise, and Lemma 26b from held votes with `R := B`: the first
disjunct.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses; `s'`: the slot of the vote; `u`: the voter.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s'` is at most `T`, so the committee of `s' − 1` is among those
  `P.hSleepK` covers.

Read aloud: at a timely slot, when the previous votes are on `B`'s chain whenever the voter is not
justified past `B` and its finalized block is `B` or an ancestor of `B`, an honest active voter
votes on `B`'s chain, or votes for a block compatible with `B` and is justified past `B`. -/
theorem vote_compatible_of_timely_view_ofExtend (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (u : V)
    -- the support cutoff of `s'` is at most `T`
    (hT : M.supportCutoff S.C s' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep u (M.voteTime S.C s')))))
    (hs' : s + 2 ≤ s') (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ s')
    (hu : u ∈ honestActiveAt M S A x s')
    (hC : CachesCompatibleWith M S B H (x.tickInput u (M.voteTime S.C s')))
    (hTwo : ∀ D ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : M.fg_contest (x.tickInput u (M.voteTime S.C s')) = false ∨
      (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput u (M.voteTime S.C s')))
    (hExt : (x.tickInput u (M.voteTime S.C s')).justifiedHeight ≤ (M.chainStateOf S.C B).h →
      (x.tickInput u (M.voteTime S.C s')).finalized.AncestorEq B →
      VotesExtendAt M S A x s B Δs b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk u s' H_u.root ∧
        (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
          (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput u (M.voteTime S.C s')).justifiedHeight))
              := by
  intro vote hsend
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hExt
  obtain ⟨-, hJB, -, hJh, hFJ⟩ := hC
  -- `u`'s state before its vote satisfies the model's node invariant (Lemma 11)
  obtain ⟨i₀, hl₀, -⟩ := id hsend
  have hTI : x.tickInput u (M.voteTime S.C (σ + 1)) = x.st i₀ u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl₀]
  have hui₀ : u ∉ A.corrupted i₀ := E.not_mem_corrupted_of_tick hl₀
  have hInvU : M.nodeInv S.C S.P S.X (x.tickInput u (M.voteTime S.C (σ + 1))) := by
    rw [hTI]; exact ((lem11_node_invariant M F) S A x R E i₀ u hui₀).1
  -- the case the voter is justified past `B`
  by_cases hjust : (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput u (M.voteTime S.C (σ + 1))).justifiedHeight
  · -- the walk of `u`'s vote starts at the anchor over its frame with some lock entries `Eb`, the
    -- fgroot or a block of the viable tree (`anchorAt_cases`)
    obtain ⟨Eb, H_u, hHT, hveq, votes, sv, -, hWalk⟩ := (tick_vote_fork_choice M F U R E) (σ + 1) u vote hsend
    exact ⟨H_u, hHT, hveq, Or.inr ⟨(GoldilocksCorrectness.Record.Proofs.Routines.vote_head_compatible_of_justified_past M F)
      S.C S.P S.X _ hInvU B hJB hJh hFJ hTwo (by rw [hTI]; exact (h_j_lt_h_max_st M F) S A x R E i₀ u) hjust _
      (GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M _ Eb _) _ _ votes sv _ H_u hWalk.1, hjust⟩⟩
  -- the case `B` is a strict ancestor of the voter's finalized block
  by_cases hFB : (x.tickInput u (M.voteTime S.C (σ + 1))).finalized.AncestorEq B
  swap
  · have hBF : B.AncestorEq (x.tickInput u (M.voteTime S.C (σ + 1))).finalized := by
      rcases hJB with hJB' | hBJ
      · exact absurd (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFJ hJB') hFB
      · rcases GoldilocksCorrectness.Proofs.Routines.ancestorEq_compatible hFJ hBJ with h | h
        · exact absurd h hFB
        · exact h
    obtain ⟨Eb, H_u, hHT, hveq, votes, sv, -, hWalk⟩ := (tick_vote_fork_choice M F U R E) (σ + 1) u vote hsend
    exact ⟨H_u, hHT, hveq, Or.inl (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hBF
      ((GoldilocksCorrectness.Record.Proofs.Routines.vote_head_descends_of_F M F) S.C S.P S.X _ hInvU hFJ _
        (GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M _ Eb _) _ _ votes sv _ H_u hWalk.1))⟩
  -- the case the voter's finalized block is `B` or an ancestor of `B`: Lemma 26b from held votes
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hjle : (x.tickInput u (M.voteTime S.C (σ + 1))).justifiedHeight ≤ (M.chainStateOf S.C B).h := by
    omega_nat
  -- not contested
  have hNC' : M.fg_contest (x.tickInput u (M.voteTime S.C (σ + 1))) = false := by
    rcases hNC with h | h
    · exact h
    · cases hc : M.fg_contest (x.tickInput u (M.voteTime S.C (σ + 1)))
      · rfl
      · have hm := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_of_contested M F) S.C S.P S.X _ hInvU hc
        omega_nat
  -- the times of slots `σ`, `σ + 1`, `σ + 2`, over the atom `slotStart S σ`
  have hss1 : M.slotStart S.C (σ + 1) = M.slotStart S.C σ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (σ + 1 + 1) = M.slotStart S.C (σ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hvtσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hscσ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have hvfσ := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S σ
  have hvt1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hsc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hvt2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1 + 1)
  have hsc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1 + 1)
  -- the votes of slot `σ` are on `B`'s chain
  have hExt := hExt hjle hFB
  -- the voters, their majority and their blocks
  obtain ⟨Q, hQsub, hQext, hQcard⟩ := (voters_on_chain_majority M F U) P σ (by omega) (by omega) hExt
  obtain ⟨Hf, hHs⟩ := (exists_votes_on_chain M F U) S A x R σ Q B E hSkew hQsub hQext
  have hcard : (S.P.committee σ).card < 2 * Q.card := by
    have := Finset.card_le_card_sdiff_add_card (s := S.P.committee σ) (t := Q)
    omega
  obtain ⟨u₀, hu₀⟩ : Q.Nonempty := Finset.card_pos.1 (by omega)
  have hFH : ∀ u' ∈ Q, (x.tickInput u (M.voteTime S.C (σ + 1))).finalized.AncestorEq (Hf u') :=
    fun u' hu' => GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFB (hHs u' hu').2.2.2.2
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- `u`'s tick to the vote time of `σ + 1` is at a real time at most `ΔClockBehind` after it, before the support
  -- cutoff of `σ + 1`; the voters of `Q` are outside the adversary set up to that cutoff, so at that tick
  have hti₀ := (E.tick_active i₀ u _ hl₀).2.2
  have hsc1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S := by
    rw [hsc1]; push_cast; ring
  have hQk : ∀ u' ∈ Q, u' ∉ A.corrupted i₀ := fun u' hu' =>
    (not_mem_corrupted_of_le_time M) x R E (hHs u' hu').2.1 (by linarith)
  have hGSTσ : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ := le_trans P.hGST
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  have hgood' : M.supportCutoff S.C σ ≤ b₀ ∨ b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C σ + Δ S := by
    unfold VotesOwedInPeriod at hgood
    simp only [Nat.add_sub_cancel] at hgood
    omega
  -- `u` is active from the duty window's start of `σ + 1` up to its tick to the support cutoff of `σ + 1` (a tick
  -- strictly inside its window, `hSkew`), so it ticks to the support cutoff of `σ`, active from Lemma 12's read
  -- time on (`updater_reader_gives_core_window`)
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hdw1 := duty_window_start_real S (σ + 1)
  push_cast at hdw1
  have hssσ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ
  have hσR : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 6 * Δ S := by
    rw [hsc1, hvt1, hss1, hssσ]; push_cast; ring
  have hσ2R : ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 10 * Δ S := by
    rw [hsc2, hvt2, hss2, hss1, hssσ]; push_cast; ring
  have hkR : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by
    have : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ hk
    exact_mod_cast (by omega : 8 * Δ S ≤ 4 * Δ S * S.C.k)
  have hu1 : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (M.supportCutoff S.C (σ + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (σ + 1) u E hu)
      (by omega) (by rw [hdw1, hσR]; push_cast; nlinarith) (by rw [hσR, hσ2R]; linarith)
  have hwσ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew (s := σ) hu1
  -- every voter of `Q` holds through Lemma 12's sync delay at slot `σ` (an updater of `σ`)
  have hHoldQ : ∀ u' ∈ Q, u' ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun u' hu' =>
    (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGSTσ
      ((honestActiveAt_subset_updaterAt M F) S A x R E σ (Finset.mem_inter.1 (hQsub hu')).1)
  -- roots up to `u`'s tick to the support cutoff of `σ`, at a real time before the vote time of `σ + 1`
  have hRootsσ : RootsNameBlocksUntil M A x (x.time (x.tickStep u (M.supportCutoff S.C σ))) := by
    obtain ⟨kR, hkR', -⟩ := hwσ
    rw [(tickStep_eq_of_lbl M) x E hkR']
    have h1 := (E.tick_active kR u _ hkR').2.2
    have h2 : ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : M.supportCutoff S.C σ + Δ S ≤ M.voteTime S.C (σ + 1))
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (le_trans (by linarith) (le_max_left _ _)) hRoots
  have hHsσ : ∀ u' ∈ Q, u' ∈ S.P.committee σ ∧ u' ∉ A.corrupted i₀ ∧
      (∃ i : ℕ, x.lbl i = Event.tick u' (M.voteTime S.C σ) ∧
        (⟨u', NamedObject.gfVote (GoldfishVote.mk u' σ (Hf u').root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      Hf u' ∈ (x.tickInput u' (M.voteTime S.C σ)).tree := fun u' hu' =>
    ⟨(hHs u' hu').1, hQk u' hu', (hHs u' hu').2.2.1, (hHs u' hu').2.2.2.1⟩
  -- the votes of `Q` held by `u` at its tick to the vote time of `σ + 1`, stamped and resolved before `tb`
  obtain ⟨tb, htb, hHeld⟩ : ∃ tb : ℕ, tb ≤ M.viewFreeze S.C σ ∧ ∀ u' ∈ Q,
      HeldEarlyVoteAt M (x.tickInput u (M.voteTime S.C (σ + 1))) ((tb : ℕ) : Int) σ (Hf u') u' := by
    have hcv : M.supportCutoff S.C σ ≤ M.voteTime S.C (σ + 1) := by omega
    rcases hgood' with hb | hb
    · -- before the period: Lemma 12 bounded up to the support cutoff of `σ`, at `u`'s tick
      refine ⟨M.supportCutoff S.C σ, by omega, fun u' hu' => ?_⟩
      have h := (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST σ (M.voteTime S.C (σ + 1)) Q Hf u
        ((envFactsBy_of_synchronyFromWakeUpTo M) x E (((synchronyFromWakeUpTo_of_outside M) P.hSync).mono M hb))
        hNet hSkew hRedeliver (P.Sy.upTo.mono hb) hΔs hRootsσ P.hParent (votesCastByOwner_of_unforgeability M F S A x R E)
        hGSTσ hcv i₀ hl₀ hHsσ hHoldQ hwσ hFH u' hu'
      rw [(GoldilocksCorrectness.Record.Statements.Executions.heldEarlyVoteFor_iff M), ← (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)] at h
      exact h
    have hGSTb : GST ≤ b₁ := by
      have h1 := P.hGST
      have h2 := P.hb₀
      have h3 := P.hb
      omega
    rcases Nat.lt_or_ge (M.supportCutoff S.C σ) (b₁ + max (Δ S) Δs) with hlate | hearly
    · -- the period plus its recovery ends in `(M.supportCutoff S.C σ, M.viewFreeze S.C σ]`: Lemma 12 by a later delay
      -- (`lem12_honest_vote_delivered_by_until`,) at the window `[t, t + Δ S]`, `t + Δ S = b₁ + max (Δ S) Δs`,
      -- from `max b₁ GST`, at `u`'s tick to the vote time of `σ + 1`
      obtain ⟨t, ht⟩ : ∃ t : ℕ, t + Δ S = b₁ + max (Δ S) Δs :=
        ⟨_, Nat.sub_add_cancel (le_trans (le_max_left _ _) (Nat.le_add_left _ _))⟩
      refine ⟨t + Δ S, by omega, ?_⟩
      have hmx : max (2 * Δ S) Δs ≤ t + Δ S := by
        have := le_max_right (Δ S) Δs
        rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
      have hcσR : ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 2 * Δ S := by
        rw [hscσ, hvtσ, hssσ]; push_cast; ring
      have hvtσR : ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + Δ S := by
        rw [hvtσ, hssσ]; push_cast; ring
      have he1 : ((M.supportCutoff S.C σ : ℕ) : ℝ) + 1 ≤ ((t + Δ S : ℕ) : ℝ) := by
        exact_mod_cast (by omega : M.supportCutoff S.C σ + 1 ≤ t + Δ S)
      have he2 : ((t + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S := by
        exact_mod_cast (by omega : t + Δ S ≤ M.supportCutoff S.C σ + Δ S)
      have hA1 : ΔClockAhead < Δ S := by linarith
      have hB1 : ΔClockBehind < Δ S := by linarith
      -- the read time `t + Δ S − max (2 * Δ S) Δs` and the earlier of it and the vote time of `σ`, as real numbers
      set rt : ℕ := t + Δ S - max (2 * Δ S) Δs with hrt
      have hrtΔs : (rt : ℝ) + Δs ≤ ((t + Δ S : ℕ) : ℝ) := by
        have := le_max_right (2 * Δ S) Δs
        exact_mod_cast (by omega : rt + Δs ≤ t + Δ S)
      -- the duty window of `σ + 1` opens more than `ΔClockBehind` before the earlier of the vote time and the read time
      have hstart : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) + ΔClockBehind <
          min ((M.voteTime S.C σ : ℕ) : ℝ) (rt : ℝ) := by
        rw [hdw1]
        refine lt_min (by rw [hvtσR]; push_cast; linarith) ?_
        rcases le_total (2 * Δ S) Δs with h2 | h2
        · have hr : (rt : ℝ) + Δs = ((t + Δ S : ℕ) : ℝ) := by
            rw [hrt, max_eq_right h2]; exact_mod_cast (by omega : t + Δ S - Δs + Δs = t + Δ S)
          have hm : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_right _ _
          push_cast; linarith
        · have hr : (rt : ℝ) + 2 * Δ S = ((t + Δ S : ℕ) : ℝ) := by
            rw [hrt, max_eq_left h2]
            exact_mod_cast (by omega : t + Δ S - 2 * Δ S + 2 * Δ S = t + Δ S)
          push_cast; linarith
      -- `u` ticks to `t + Δ S`, active from that earlier time up to the tick
      have hu' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (t + Δ S) :=
        (mem_activeThroughoutToTick_of_inside M F) R E hu1 (by omega)
          (by rw [hdw1]; linarith) (by rw [hσR]; linarith)
      have hw' := (tick_window_of_activeThroughoutToTick_int M) x R E hu'
        (t₀ := min ((M.voteTime S.C σ : ℕ) : ℝ) (rt : ℝ)) hstart
      obtain ⟨kR, hkR, -⟩ := hw'
      -- roots up to `u`'s tick to `t + Δ S`, at a real time before the vote time of `σ + 1`
      have hRoots' : RootsNameBlocksUntil M A x (x.time (x.tickStep u (t + Δ S))) := by
        rw [(tickStep_eq_of_lbl M) x E hkR]
        have h1 := (E.tick_active kR u _ hkR).2.2
        have h2 : ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S + Δ S ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : M.supportCutoff S.C σ + Δ S + Δ S ≤ M.voteTime S.C (σ + 1))
        exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (le_trans (by linarith) (le_max_left _ _)) hRoots
      -- each voter's tick to the vote time of `σ` is at a real time at least that vote time minus `ΔClockAhead`
      have hvtick : ∀ u' ∈ Q, ((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead ≤ x.time (x.tickStep u' (M.voteTime S.C σ)) :=
        fun u' hu' => by
          obtain ⟨i', hi', -⟩ := (hHs u' hu').2.2.1
          rw [(tickStep_eq_of_lbl M) x E hi']
          exact (E.tick_active i' u' _ hi').2.1
      -- the duty window of `σ + 1` opens more than `ΔClockBehind` before the earlier of the vote time minus
      -- `ΔClockAhead` and the read time
      have hstart1 : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) + ΔClockBehind <
          min (((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead) (rt : ℝ) := by
        refine lt_min ?_ (lt_min_iff.1 hstart).2
        rw [hdw1, hvtσR]; push_cast; nlinarith
      have hmin : ∀ u' ∈ Q, min (((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead) (rt : ℝ) ≤
          min (x.time (x.tickStep u' (M.voteTime S.C σ))) (rt : ℝ) := fun u' hu' =>
        min_le_min (hvtick u' hu') le_rfl
      -- every voter of `Q`, an updater of `σ`, is active for the sync delay from the earlier of its own vote tick
      -- and the read time (per voter, as amended by)
      have hHoldQ' : ∀ u' ∈ Q, u' ∈ A.activeThroughout x (min (x.time (x.tickStep u' (M.voteTime S.C σ))) (rt : ℝ))
          (((⌈min (x.time (x.tickStep u' (M.voteTime S.C σ))) (rt : ℝ)⌉₊ : ℕ) : ℝ) + Δs) := fun u' hu' =>
        (mem_activeThroughout_of_mem_activeThroughoutToTick_real M F) R E
          ((honestActiveAt_subset_updaterAt M F) S A x R E σ (Finset.mem_inter.1 (hQsub hu')).1)
          (lt_of_lt_of_le hstart1 (hmin u' hu'))
          (by
            have h1 : ((⌈min (x.time (x.tickStep u' (M.voteTime S.C σ))) (rt : ℝ)⌉₊ : ℕ) : ℝ) ≤ (rt : ℝ) := by
              exact_mod_cast Nat.ceil_le.2 (min_le_right (x.time (x.tickStep u' (M.voteTime S.C σ))) (rt : ℝ))
            have hle : ((t + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S := he2
            rw [hσR]; rw [hcσR] at hle; linarith)
      -- `u` is active from the earliest of those times up to its tick to `t + Δ S`
      have hwQ : ∃ kR : ℕ, x.lbl kR = Event.tick u (t + Δ S) ∧ ∀ u' ∈ Q, ∀ j : ℕ,
          min (x.time (x.tickStep u' (M.voteTime S.C σ))) (rt : ℝ) ≤ x.time j → j ≤ kR → u ∈ A.active j := by
        obtain ⟨kR, hkR1, hact⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hu' hstart1
        exact ⟨kR, hkR1, fun u' hu'' j hj hjk => hact j (le_trans (hmin u' hu'') hj) hjk⟩
      have h := (lem12_honest_vote_delivered_by_until M F U) S A x R (max b₁ GST) σ t (M.voteTime S.C (σ + 1)) Q Hf u
        ((envFactsBy_of_synchronyFromWakeBy M) x E ((synchronyFromWake_of_outside_after M) P.hSync))
        hNet hSkew hRedeliver ((syncedWithin_after_period_of_outside M F) P.Sy) hRoots' P.hParent
        (votesCastByOwner_of_unforgeability M F S A x R E) (by omega) (by omega) (by omega) (by omega) i₀ hl₀ hHsσ
        hHoldQ' hwQ hFH
      exact h
    · -- it ends by the support cutoff of `σ`: Lemma 12 at `u`'s tick from `max b₁ GST`
      refine ⟨M.supportCutoff S.C σ, by omega, fun u' hu' => ?_⟩
      have h := (lem12_honest_vote_delivered_until_of_steps M F U) S A x R (max b₁ GST) σ (M.voteTime S.C (σ + 1)) Q Hf u
        ((envFactsBy_of_synchronyFromWakeBy M) x E ((synchronyFromWake_of_outside_after M) P.hSync))
        hNet hSkew hRedeliver ((syncedWithin_after_period_of_outside M F) P.Sy) hΔs hRootsσ P.hParent
        (votesCastByOwner_of_unforgeability M F S A x R E) (by omega) hcv i₀ hl₀ hHsσ hHoldQ hwσ hFH u' hu'
      rw [(GoldilocksCorrectness.Record.Statements.Executions.heldEarlyVoteFor_iff M), ← (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)] at h
      exact h
  -- `hF3`: a viable head of the voter tree on `B`'s chain
  have hfl : M.head_height_floor (x.tickInput u (M.voteTime S.C (σ + 1))) =
      hMax M S.C (x.tickInput u (M.voteTime S.C (σ + 1))) - 1 :=
    (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X _ hInvU hNC'
  have hF3 : (M.fg_to_ac (x.tickInput u (M.voteTime S.C (σ + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput u (M.voteTime S.C (σ + 1))) (S.C.t_ ((σ + 1) - 1) + 3 * S.C.Δ) (σ + 1) W ∧ W ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C (σ + 1)))).viable_heads ∧
          B.AncestorEq W := by
    intro hrB
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hrB
    by_cases h2 : (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput u (M.voteTime S.C (σ + 1)))
    · -- the certified entry one height less than the top height (Lemma 67), held by `u` at its tick to the view
      -- freeze of `σ` (`cert_entry_held_before_freeze`,), in the voter tree at its tick to the vote time
      -- of `σ + 1` (`mem_voter_tree_st`,)
      obtain ⟨-, ⟨Z, hZT, hZh⟩, -⟩ : GoldilocksCorrectness.Record.Proofs.Routines.CachesWitnessed M S.C (x.tickInput u (M.voteTime S.C (σ + 1))) := by
        rw [hTI]; exact (cachesWitnessed_of_exec M F) S A x R E i₀ u
      have hBZ : B.AncestorEq Z := hTwo Z hZT (by rw [hZh]; exact h2)
      obtain ⟨Y, hYZ, -, hYp, -, hTY, hcert⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.lem67_first_advance M F) S.C Z
          (hMax M S.C (x.tickInput u (M.voteTime S.C (σ + 1))) - 1) (by omega_nat)
          (by rw [hZh]; omega_nat)
      have hT'h : (M.chainStateOf S.C (M.chainStateOf S.C Y.parent).T_h).h =
          hMax M S.C (x.tickInput u (M.voteTime S.C (σ + 1))) - 1 := by
        rw [((GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C Y.parent).2.1, hYp]
      have hT'Z := GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hTY hYZ
      have hYT : Y ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ u Z Y hZT hYZ
      have hT'T : (M.chainStateOf S.C Y.parent).T_h ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ u Z _ hZT hT'Z
      have hBT' : B.AncestorEq (M.chainStateOf S.C Y.parent).T_h := by
        rcases GoldilocksCorrectness.Proofs.Routines.ancestorEq_compatible hBZ hT'Z with h | h
        · exact h
        · have hm := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
          omega_nat
      have hFT' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFB hBT'
      have hFT'i : (x.st i₀ u).finalized.AncestorEq (M.chainStateOf S.C Y.parent).T_h := by
        rw [← hTI]; exact hFT'
      -- `u`'s tick to the view freeze of `σ`, inside its window, before its tick to the vote time of `σ + 1`
      have hvfR : ((M.viewFreeze S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 3 * Δ S := by
        rw [hvfσ, hssσ]; push_cast; ring
      have hdwsR : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) ≤ 4 * Δ S * (σ : ℝ) := by
        have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart
          M.toSlotLayout F.sched) S σ
        have h2 : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C σ : ℕ) : ℝ) := by
          exact_mod_cast h1
        rw [hssσ] at h2; push_cast at h2; exact h2
      obtain ⟨kf, hkf, -, -⟩ := (tick_of_honestActiveAt M F U) R E (t := M.viewFreeze S.C σ) hu
        (by rw [hvfσ]; omega) (by rw [hvfR]; linarith) (by rw [hvfR, hσ2R]; linarith)
      have hkfi : x.tickStep u (M.viewFreeze S.C σ) < i₀ := by
        have h := (tickStep_viewFreeze_lt_tickStep_voteTime_succ M F U) x R E hSkew ⟨kf, hkf⟩ ⟨i₀, hl₀⟩
        rwa [(tickStep_eq_of_lbl M) x E hl₀] at h
      have hTR : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      have hFvf : (x.tickInput u (M.viewFreeze S.C (σ + 1 - 1))).finalized.compatible
          (M.chainStateOf S.C Y.parent).T_h = true := by
        rw [Nat.add_sub_cancel]
        unfold Trace.tickInput
        exact (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2
          (Or.inl (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans
            ((grows_of_le M F) x R E u hkfi.le).2.1 hFT'i))
      have hheld := (cert_entry_held_before_freeze M F U Fx R E hNet hSkew hRedeliver hΔs) P (σ + 1) u Y
        (M.chainStateOf S.C Y.parent).T_h (hMax M S.C (x.tickInput u (M.voteTime S.C (σ + 1))) - 1)
        (by rw [(tickStep_eq_of_lbl M) x E hl₀]; exact max_le (by linarith) (by linarith))
        hRoots hs' hgood hu hYT hTY hcert (by rw [hT'h]; omega_nat) hFvf
      rw [Nat.add_sub_cancel] at hheld
      -- the clock value at `u`'s tick to the view freeze is less than it
      have hck : x.clockValue (x.tickStep u (M.viewFreeze S.C σ)) u < M.viewFreeze S.C (σ + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        refine (clockValue_lt_at_tickStep_of_activeThroughoutToTick M F) x R E hu1 (by rw [hvfσ]; omega) ?_ ?_ ⟨kf, hkf⟩
        · rw [hdw1, hvfR]; linarith
        · rw [hvfR, hσR]; linarith
      have hmem := (mem_voter_tree_st M F U) S A x R E hkfi.le hui₀ hheld hck hFT'i
      refine ⟨_, (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _ _).1
        (by rw [hTI]; exact hmem),
        (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_of M F) S.C S.P S.X _ hInvU _ hT'T hFT'
          (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hrB hBT')
          (by rw [hfl, hT'h]), hBT'⟩
    · -- `B` itself, held, stamped before the view freeze, viable
      obtain ⟨-, -, hHΦ, ⟨y, hy, hyb⟩, -⟩ := hHeld u₀ hu₀
      have hHT : Hf u₀ ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree :=
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).1
      have hBH : B.AncestorEq (Hf u₀) := (hHs u₀ hu₀).2.2.2.2
      have hBT : B ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ u _ B hHT hBH
      have hBΦ : B ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C (σ + 1)))).tree :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBT, hFB⟩
      have h23 : ((((tb : ℕ) : Int) : Time) : Stamp) ≤ ((S.C.t_ σ + 3 * S.C.Δ : Time) : Stamp) := by
        apply WithBot.coe_le_coe.2
        rw [← (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
        exact_mod_cast htb
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := (ancestor_blockStamp_le M F) S A x R E _ u (Hf u₀) B hHT hBH
      -- the vote resolves at the later of its stamp and the stamp of the block its head names, which
      -- is `Hf u₀` (roots name blocks in the frame's tree)
      obtain ⟨τv, τH', H', -, hH'Φ, hroot', -, hτH', rfl⟩ := hy
      obtain rfl : Hf u₀ = H' :=
        ((GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ u)
          _ hHΦ H' hH'Φ hroot'.symm
      have hle' : τH' ≤ max τv τH' := le_max_right _ _
      have hτHH' : τH = τH' := Option.some_injective _ (hτH.symm.trans hτH')
      obtain ⟨y', hyy', hy'lt⟩ :=
        (GoldilocksCorrectness.Proofs.Routines.occurrenceBefore_eq_true_iff _ _).1 hyb
      have hyy : max τv τH' = y' := Option.some_injective _ hyy'
      have hτlt : τP < ((S.C.t_ σ + 3 * S.C.Δ : Time) : Stamp) :=
        lt_of_le_of_lt hle (hτHH' ▸ lt_of_le_of_lt hle' (hyy ▸ lt_of_lt_of_le hy'lt h23))
      refine ⟨B, ⟨hBΦ, τP, hτP, Or.inl ?_⟩,
        (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_of M F) S.C S.P S.X _ hInvU _ hBT hFB hrB
          (by rw [hfl]; omega_nat),
        GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl B⟩
      rw [Nat.add_sub_cancel]
      exact hτlt
  -- Lemma 26b from held votes, with `R := B`, the voters outside the adversary set at `u`'s tick step
  obtain ⟨H_w, hT, hv, hB⟩ :=
    (lem26b_goldfish_vote_extends_voter_majority_block_of_held M F U)
      S A x R σ tb Q Hf B u vote E (votesCastByOwner_of_unforgeability M F S A x R E) htb
      (fun u' hu' => ⟨(tickStep_eq_of_lbl M) x E hl₀ ▸ hQk u' hu', (hHs u' hu').2.2.1, (hHs u' hu').2.2.2.2⟩)
      (fun _ => hHeld)
      (fun votes sv hCV => (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
        ((countedVotes_committee_st M F) S A x R E _ σ u votes sv hCV) hQcard)
      (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_compatible M F) S.C S.P S.X _ hInvU B hJB hFJ) hF3
      -- the revocation every outcome of `u`'s tick at the vote time ran (`locksRevoked_of_voteTime_outcome`)
      (fun _ n' sent hrun hAw => (revoked_entries_compatible_of_majority_tick M F) S A x R E σ tb u Q Hf B hcard
        (fun u' hu' => (hHs u' hu').2.2.2.2) hHeld n'
        ((locksRevoked_of_voteTime_outcome M F U) S A x R E (σ + 1) u n' sent hrun hAw))
      hsend
  exact ⟨H_w, hT, hv, Or.inl hB⟩
/-- **Statement 1′: the vote of a timely slot is on `B`'s chain, or compatible with `B` from a
voter justified past `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`.
`vote_compatible_of_timely_view_ofExtend`, with the votes of `σ := s' − 1` on `B`'s chain when the
voter `u` is not justified past `B` and its finalized block is `B` or an ancestor of `B`: the
holders' when the votes of `σ − 1` were owed (`hVotes.1`, `σ ≤ s + k` by `owed_slot_le_k`), and
every honest active voter's otherwise, since one with the second disjunct would, by
`justified_past_spreads` (`hCprev`), give `u` a justification height at least `h(B) + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses; `s'`: the slot of the vote; `u`: the voter.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s'` is at most `T`, so the committee of `s' − 1` is among those
  `P.hSleepK` covers.

Read aloud: at a timely slot, an honest active voter votes on `B`'s chain, or votes for a block that
does not conflict with `B` with its finality gadget justified past `B`. -/
theorem vote_compatible_of_timely_view (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (u : V)
    -- the support cutoff of `s'` is at most `T`
    (hT : M.supportCutoff S.C s' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep u (M.voteTime S.C s')))))
    (hs' : s + 2 ≤ s') (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ s')
    (hu : u ∈ honestActiveAt M S A x s')
    (hC : CachesCompatibleWith M S B H (x.tickInput u (M.voteTime S.C s')))
    (hTwo : ∀ D ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : M.fg_contest (x.tickInput u (M.voteTime S.C s')) = false ∨
      (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput u (M.voteTime S.C s')))
    (hCprev : ∀ w ∈ honestActiveAt M S A x (s' - 1),
      CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C (s' - 1))))
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk u s' H_u.root ∧
        (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
          (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput u (M.voteTime S.C s')).justifiedHeight))
              := by
  refine (vote_compatible_of_timely_view_ofExtend M F U Fx R E hNet hSkew hRedeliver hΔs) P s' u hT hRoots hs' hgood hu hC hTwo hNC ?_
  intro hjle hFB
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hCprev hVotes ⊢
  have hActive : ¬ VotesOwedInPeriod M S Δs b₀ b₁ σ → ∀ w ∈ honestActiveAt M S A x σ,
      ∀ vote' : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C σ) ∧
        (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_w ∈ (x.tickInput w (M.voteTime S.C σ)).tree,
        vote' = GoldfishVote.mk w σ H_w.root ∧ B.AncestorEq H_w := by
    intro hgσ w hw vote' hsend'
    obtain ⟨H_w, hT, hv, hB | ⟨-, hjw⟩⟩ := hVotes.2 hgσ w hw vote' hsend'
    · exact ⟨H_w, hT, hv, hB⟩
    · exfalso
      have hsp := (justified_past_spreads M F U R E hNet hSkew hRedeliver hΔs) P σ w u ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_left _ _) hRoots) (by omega) hgood hw (hCprev w hw) hjw hu
        hFB
      omega_nat
  refine ⟨fun w hw vote' hsend' => ?_, hActive⟩
  by_cases hOw : VotesOwedInPeriod M S Δs b₀ b₁ σ
  · exact hVotes.1 ((owed_slot_le_k M F U) P.hb₁ hOw) w hw vote' hsend'
  · exact hActive hOw w (Finset.mem_inter.1 hw).2 vote' hsend'

/-! ## The updates of the period's updaters -/

/-- Statement 2′ for an updater of the slot: the proof of `confirmation_compatible_of_timely_votes`
with `v ∈ updaterAt M S Sched s'` (awake and honest from the duty window of slot `s' + 1` up to its
tick to that slot's cutoff) in place of `v ∈ honestActiveAt M S Sched s'`; Lemma 78c reads only that window. The
induction reads it at a lock holder's own update after the lock's deadline.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot; `v`: the updater.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s' + 1` is at most `T`, so the committee of `s'` is
  among those `P.hSleepK` covers.

Read aloud: once the votes of a slot are due by its support cutoff, no confirmation an updater of
that slot saves conflicts with `B`. -/
theorem confirmation_compatible_of_updater (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (v : V)
    -- the committee of slot `s'` is among those `P` counts
    (hT : M.supportCutoff S.C (s' + 1) ≤ T)
    -- roots name blocks among what honest validators hold up to the real time of `v`'s own tick to the support
    -- cutoff of `s'`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s'))))
    (hs' : s + 1 ≤ s') (hgood : VotesDueByCutoff M S Δs b₀ b₁ s')
    -- `v` ticks to the support cutoff of slot `s' + 1`, awake and honest from the duty window's
    -- start of slot `s' + 1` up to that tick
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.supportCutoff S.C (s' + 1)))
    (hF : (x.tickInput v (M.supportCutoff S.C (s' + 1))).finalized.compatible B = true)
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C'.compatible B = true := by
  obtain ⟨Q, hQsub, hQext, hQcard⟩ := (voters_compatible_majority M F U) P s' hT hs' hVotes
  obtain ⟨Hf, hHs₀⟩ := (exists_votes_compatible M F U) S A x R s' Q B E hSkew hQsub hQext
  -- the voters are honest at `v`'s tick to the support cutoff of `s' + 1`
  have hHs : ∀ u ∈ Q, u ∈ S.P.committee s' ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s' + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' (Hf u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      Hf u ∈ (x.tickInput u (M.voteTime S.C s')).tree ∧ (Hf u).compatible B = true := fun u hu =>
    ⟨(hHs₀ u hu).1, (not_mem_corrupted_tickStep_of_honestActiveAt M F) E (Finset.mem_inter.1 (hQsub hu)).1 hv,
      (hHs₀ u hu).2.2⟩
  have hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') <
      2 * Q.card :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v s') hQcard
  have hv' := hv
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s' := le_trans P.hGST
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  -- every voter is active through the sync fact's window at slot `s'`: its duty window
  -- (`honestActiveAt_window`) holds the window (`holder_window_of_updater_reader`)
  have hHold : ∀ u ∈ Q, u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun u hu =>
    (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGSTs
      (GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_activeThroughoutToTick_of_le
        ((duty_window_start_le_of_le M F U) S (Nat.le_succ s'))
        ((honestActiveAt_window M F) S A s' u E (Finset.mem_inter.1 (hQsub hu)).1))
  rcases hgood with hA | hB
  · -- before the period: the bounded delivery promise and the sync fact up to `b₀`
    exact (lem78c_update_confirmation_compatible_of_voter_majority_upTo M F U)
      S A x R GST s' Q Hf B v
      ((envFactsBy_of_synchronyFromWakeUpTo M) x E (((synchronyFromWakeUpTo_of_outside M) P.hSync).mono M hA))
      hNet hSkew hRedeliver (P.Sy.upTo.mono hA) hΔs
      hRoots P.hParent (votesCastByOwner_of_unforgeability M F S A x R E) hGSTs hHs hHold hVoters hv' hF
  · -- after the period plus its recovery: the synchronous promise and the sync fact from `max b₁ GST`
    exact (lem78c_update_confirmation_compatible_of_voter_majority M F U)
      S A x R (max b₁ GST) s' Q Hf B v
      ((envFactsBy_of_synchronyFromWakeBy M) x E ((synchronyFromWake_of_outside_after M) P.hSync))
      hNet hSkew hRedeliver ((syncedWithin_after_period_of_outside M F) P.Sy) hΔs
      hRoots P.hParent (votesCastByOwner_of_unforgeability M F S A x R E) (by omega) hHs hHold hVoters hv' hF

/-- A validator whose tick at the support cutoff of slot `s' + 1` runs the update (its tick starting
from a record of awakeness since the duty window's start of `s' + 1` or earlier) is an updater of slot
`s'`: the reader `updaterAt` counts it up to that tick, where the environment reads it active. The step of `attest_source_fast_block_updater`'s proof.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step of the tick; `s'`: the
  slot; `v`: the validator; `τ`: the record of awakeness.

Read aloud: a validator whose tick at the support cutoff of slot `s' + 1` runs the update is an
updater of slot `s'`. -/
theorem updaterAt_of_update_tick (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i s' : ℕ) (v : V) (τ : Time)
    (hl : x.lbl i = Event.tick v (M.supportCutoff S.C (s' + 1)))
    (hτ : (x.tickInput v (M.supportCutoff S.C (s' + 1))).awakeSince = some τ)
    (hτle : τ ≤ duty_window_start S.C (s' + 1)) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.supportCutoff S.C (s' + 1)) := by
  -- the stored wake time is the initial one, `v` awake after every step up to its tick, or the value
  -- `τ ≤ duty_window_start S.C (s' + 1)` of a tick before it after the last restart, `v` awake from that
  -- tick on (`awake_of_tickInput_awakeSince_of_tick`): the reader's two cases
  have hcases := (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨i, hl⟩ hτ
  rw [(tickStep_eq_of_lbl M) x E hl] at hcases
  refine E.mem_activeThroughoutToTick_of_awakeThroughoutToTick ?_
  rcases hcases with ⟨-, hall⟩ | ⟨k₁, τ', hk₁, hl₁, hτ', hawk⟩
  · exact Activity.mem_awakeThroughoutToTick_of_forall hl hall
  · exact Activity.mem_awakeThroughoutToTick_of_tick (hτ' ▸ hτle) hk₁.le hl hl₁ hawk

/-- The tick at `t` comes no later than step `j` when the configuration after step `j` is at the
time `t` or later.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `j`: the step.

Read aloud: the step before time `t` comes no later than any step whose configuration is at time `t`
or later. -/
theorem stepBefore_le_of_le_time {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t j : ℕ}
    (h : t ≤ x.time (j + 1)) : x.stepBefore t ≤ j := by
  by_contra hc
  have := ((lt_stepBefore_iff M) x R E).1 (show j < x.stepBefore t by omega)
  linarith

/-- At a real time `τ` before the vote time of a slot `s'` and no earlier than the support cutoff of
slot `s' − 1`, every slot whose vote time has come has reached its support cutoff: such a slot is
before `s'`, so its support cutoff is at most that of `s' − 1`. A proof-page helper of the induction
: clause 1 of the period invariant holds at the configuration before
a vote time, whose time is at least the support cutoff of the previous slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s'`: the slot; `τ`: the time, `M.supportCutoff S.C (s' − 1) ≤ τ < M.voteTime S.C s'`.

Read aloud: just before a vote time, every slot whose vote time has come has reached its support
cutoff. -/
theorem supportCutoffs_reached_before_voteTime (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {s' : ℕ} {τ : ℝ} (hτ : (M.supportCutoff S.C (s' - 1) : ℝ) ≤ τ) (hτ' : τ < M.voteTime S.C s') :
    ∀ s'' : ℕ, (M.voteTime S.C s'' : ℝ) ≤ τ → (M.supportCutoff S.C s'' : ℝ) ≤ τ := by
  intro s'' h
  have hv : M.voteTime S.C s'' < M.voteTime S.C s' := by exact_mod_cast lt_of_le_of_lt h hτ'
  have hlt : s'' + 1 ≤ s' := by
    by_contra hc
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S (show s' ≤ s'' by omega)
    omega
  have hsc : M.supportCutoff S.C s'' ≤ M.supportCutoff S.C (s' - 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  exact le_trans (by exact_mod_cast hsc) hτ

/-- **Some later step is at a real time more than `a`** (T-RC43-1): for every step `i` and real `a`, some step
`j > i` has `a < x[j].time`. Every natural number is reached (`time_div` at `⌈a⌉ + 1`) and the time never decreases
(`time_mono`). The general form of the deleted `exists_time_eq_after_of_le`, which asked a step at an integer real time.

The variables:
- `M`: the model; `F`: its facts; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `a`: the
  real time.

Read aloud: after any step, the run reaches every real time. -/
theorem exists_time_gt_after {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i : ℕ) (a : ℝ) : ∃ j : ℕ, i < j ∧ a < x.time j := by
  obtain ⟨i', hi'⟩ := E.time_div (Nat.ceil a + 1)
  refine ⟨max (i + 1) i', lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _), ?_⟩
  have h1 : x.time i' ≤ x.time (max (i + 1) i') := (time_mono M) x R (le_max_right _ _)
  have h2 : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
  have h3 : ((Nat.ceil a + 1 : ℕ) : ℝ) = (Nat.ceil a : ℝ) + 1 := by push_cast; rfl
  linarith

/-- **Some step after `i` comes after every tick to the clock value `c` and is at a real time at least `c`**
(T-RC43-1): `exists_time_gt_after` at `c + ΔClockBehind`; a tick to `c` is at a real time at most
`c + ΔClockBehind` (`tick_active`), so it comes before that step.

The variables:
- `M`: the model; `F`: its facts; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `c`: the
  clock value.

Read aloud: after any step, some step follows every tick to `c` at a real time at least `c`. -/
theorem exists_step_after_ticks {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i c : ℕ) :
    ∃ j : ℕ, i < j ∧ (∀ (k : ℕ) (w : V), x.lbl k = Event.tick w c → k < j) ∧ (c : ℝ) ≤ x.time j := by
  obtain ⟨j, hij, hj⟩ := (exists_time_gt_after M F) R E i ((c : ℝ) + ΔClockBehind)
  have hB := E.behind_nonneg
  refine ⟨j, hij, fun k w hk => ?_, by linarith⟩
  have h1 := (E.tick_active k w c hk).2.2
  by_contra hkj
  have h2 := (time_mono M) x R (Nat.le_of_not_lt hkj)
  linarith

/-- **The holder invariant in the hand-over window.** For an updater `w` of slot `s` honest through a
step `n` after its own tick to the hand-over cutoff `c = M.supportCutoff S.C (s + 1)`, at a time at most
`c + ΔClockBehind` and at
most `T`, with roots naming blocks by `x[n].time`, `HolderInvAt` holds at `n`.

Why: carried from the configuration `w`'s tick to `c` leaves (the hand-over facts' second clause) over
the steps that are not `w`'s ticks (`keepsConfirmation_of_no_tick_between`,
`holderInv_of_keepsConfirmation`) and over `w`'s ticks (Lemma 100's step `holderInv_step_ofCompat`).
Every tick in the window is to a clock value less than `c + Δ`, before the lock's deadline and the
vote time of slot `s + 2`; the caches there are the hand-over facts', and the only slot whose support
cutoff has come is `s + 1`, whose votes are the hand-over facts'. A tick of `w` at a real time before `c`
is to a clock value in `(c, c + Δ S)`, where only the expiry runs.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `w`: the updater; `n`: the step.

Read aloud: in the hand-over window, every updater that has run its hand-over update still holds
the lock on `B` (or has finalized a strict descendant of `B`) and records `B` or a descendant of `B`. -/
theorem holderInv_in_handover_window (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (hcT : M.supportCutoff S.C (s + 1) ≤ T)
    (w : V) (hw : w ∈ updaterAt M S A x s) (n : ℕ)
    (hn : x.tickStep w (M.supportCutoff S.C (s + 1)) < n) (hH : x.HonestThrough A n w)
    (hnw : x.time n ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) (hnT : x.time n ≤ T)
    -- the step is within the hand-over facts' window, or the facts cover the whole window
    (hjW : x.time n ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW)
    (hRoots : RootsNameBlocksUntil M A x (x.time n)) :
    HolderInvAt M S x s B n w := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcast : ∀ a b : ℕ, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun a b h => by exact_mod_cast h
  have hvs1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S (s + 1)
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hdl := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
    (show s + 1 + 1 ≤ s + S.C.k + 1 by omega)
  have PA := (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotesUntil.toAsyncHypsUntil
    M F U R E hNet hSkew hRedeliver) P hcT
  -- a tick at a step before `n` is to a clock value less than `c + Δ`
  have hclk : ∀ (k c' : ℕ), k < n → x.lbl k = Event.tick w c' → c' < M.supportCutoff S.C (s + 1) + Δ S :=
    fun k c' hk hl => by
      have h1 := (E.tick_active k w c' hl).2.1
      have h2 : x.time k ≤ x.time n := (time_mono M) x R hk.le
      have h3 : (c' : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h3
  -- the slots `s' ≥ s + 1` whose support cutoff is at most `x[n].time` are `s + 1`
  have hslot : ∀ s' : ℕ, s + 1 ≤ s' → (M.supportCutoff S.C s' : ℝ) ≤ x.time n → s' = s + 1 := fun s' h1 h => by
    by_contra hc'
    have e1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
      (show s + 1 + 1 ≤ s' by omega)
    have e2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
    have e3 := hcast _ _ (show M.supportCutoff S.C (s + 1) + 4 * Δ S ≤ M.supportCutoff S.C s' by omega)
    have e4 : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
    push_cast at e3
    linarith
  suffices key : ∀ m : ℕ, x.tickStep w (M.supportCutoff S.C (s + 1)) + 1 ≤ m → m ≤ n → HolderInvAt M S x s B m w from
    key n hn le_rfl
  intro m hm1
  induction m, hm1 using Nat.le_induction with
  | base => exact fun _ => (P.hHand.2.1 w hw).2.2
  | succ m hm ihm =>
    intro hmn
    have hInv := ihm (by omega)
    have hwm1 : w ∉ A.corrupted (m + 1) := hH (m + 1) hmn
    have htm1 : x.time (m + 1) ≤ x.time n := (time_mono M) x R hmn
    by_cases htk : ∃ c', x.lbl m = Event.tick w c'
    · obtain ⟨c', hl⟩ := htk
      have hwm : w ∉ A.corrupted m := E.not_mem_corrupted_of_tick hl
      have hk1 : x.time (m + 1) = x.time m := R.time_keep m (by rw [hl]; intro h; cases h)
      have hupd := (tick_honest_of_activeThroughoutToTick M F E) ((updaterAt_window M F) S A s w E hw)
      -- the tick is to a clock value after the hand-over cutoff: `w` ticked to the cutoff at an earlier step
      have hcc : M.supportCutoff S.C (s + 1) ≤ c' :=
        E.clock_mono _ m w _ _ (by omega) hwm (Or.inl hupd.1) (Or.inl hl)
      by_cases htm : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time m
      · -- Lemma 100's step at `w`'s tick
        exact (holderInv_step_ofCompat M F U R E hSkew) PA m w (le_trans htm1 hnT)
          (fun s' hl' => by
            have h1 := hclk m _ (by omega) hl'
            have h2 : s' ≤ s + 1 := by
              by_contra hc'
              have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
                (show s + 1 + 1 ≤ s' by omega)
              omega
            exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2)
              hcT)
          (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M htm1 hRoots)
          (fun c'' hl'' => by rw [hl] at hl''; cases hl''; exact hcc)
          (fun c'' keep hr => by rw [hl] at hr; cases hr)
          (fun c'' hl'' => by have := hclk m c'' (by omega) hl''; omega) hInv
          (P.hHand.2.2.1 m w htm (hjW.elim (fun h => by linarith) (fun h => by linarith)) hwm)
          (fun s' hs' h => by
            obtain rfl := hslot s' hs' (le_trans h htm1)
            exact (GoldilocksCorrectness.Record.Statements.Executions.votesCompatibleAt_of_votesExtendAt M) S A x
              (P.hHand.2.2.2.2.2.1 Δs b₀ b₁))
      · -- a tick at a real time before the hand-over cutoff, to a clock value in `(c, c + Δ S)`: nothing is
        -- due there but the expiry
        have hne : c' ≠ M.supportCutoff S.C (s + 1) := fun h => by
          subst h
          have := E.tick_unique _ _ w _ hl hupd.1
          omega
        exact (holderInv_step_idle_tick M F U R E) m w c' hl
          ((not_duty_of_cutoff_lt_lt M F U) s c' (lt_of_le_of_ne hcc (Ne.symm hne)) (hclk m c' (by omega) hl))
          (by have := hclk m c' (by omega) hl; omega) hInv
    · push Not at htk
      exact (holderInv_of_keepsConfirmation M F U R E) (Nat.le_succ m) hwm1
        (keepsConfirmation_of_no_tick_between M F x R w (Nat.le_succ m) (fun i h1 h2 t' => by
          obtain rfl : i = m := by omega
          exact htk t')) hInv

/-- **A tick at a step at a time at most `t` is to a clock value at most `T`, for `T ≥ t + ΔClockAhead`.**
A tick to the clock value `c` is at a real time at least `c − ΔClockAhead` (`tick_active`).

A proof-page helper: the
corollaries that choose the bound `T` of the bounded premises choose it at least the real time read plus
`ΔClockAhead`, and supply the induction's per-tick row with it.

Read aloud: no tick at a time at most `t` reaches a clock value more than `ΔClockAhead` after `t`. -/
theorem tick_clock_le_of_time_le {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℝ} {T : ℕ}
    -- `T` is at least `t + ΔClockAhead`
    (hT : t + ΔClockAhead ≤ T) :
    ∀ (k : ℕ) (v : V) (c : ℕ), x.time k ≤ t → x.lbl k = Event.tick v c → c ≤ T := fun k v c hk hl => by
  have h1 := (E.tick_active k v c hl).2.1
  have h2 : (c : ℝ) ≤ T := by linarith
  exact_mod_cast h2

/-! ## Statement 3′: the induction -/

/-- **The joint invariant under the compatible vote clause, from the hand-over update on.** For
every step `j` after every updater's tick to the hand-over cutoff `c = M.supportCutoff S.C (s + 1)`
and at a time at least `c`, with roots naming blocks among what honest validators hold up to
`x[j].time`, `PeriodInvCompatDueByCutoff` holds at `j`.

 the range starts at the configurations whose time is `c` once every updater
has run its update there.

Why: strong induction on the step `j`. A tick to the clock value
`t` is at a real time in `[t − ΔClockAhead, t + ΔClockBehind]` and keeps the real time. In the
hand-over window (`x[j].time` at most `c + ΔClockBehind`) clauses 3 to 5 are the hand-over facts'
(`P.hHand`); after it, `j − 1` is in the range (`hWin`: no step jumps over the window; every updater's
tick to `c` is at a time at most `c + ΔClockBehind`), and clause 5 is `attestations_step_ofHeldEntry_ofCompat`,
clause 4 the certificate step, clause 3 `caches_step_ofChainBlock`. Clause 6 at a slot `s' ≥ s + 2`:
each vote from the invariant at the voter's own tick to the vote time of `s'` (a step of the range,
at a time more than `c + ΔClockBehind` and before the support cutoff of `s'`), through
`holder_vote_extends_B_orTwoPast_ofCompat` for the holders and statement 1′ or its core for the
honest active voters. Clauses 1 and 2: each updater's holder invariant carried from the
configuration its tick to `c` leaves (`P.hHand`), over the steps that are not its ticks
(`keepsConfirmation_of_no_tick_between`, `holderInv_of_keepsConfirmation`) and over its ticks
(Lemma 100's step `holderInv_step_ofCompat`); clause 2 where the carry's conditions fail is the
record kept by the step, or `w`'s confirmation update after the lock's deadline
(`confirmation_compatible_of_updater`). Clause 7 from `confirmation_compatible_of_timely_votes` at
the validator's own tick to the support cutoff of `s' + 1`.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses.
- `T`: the time up to which `P`'s premises are read;
  the invariant is concluded at the steps whose time is at most `T` and before which every tick is to a
  clock value at most `T`.

Read aloud: at every step from the hand-over update on, the hand-over facts hold in the form with
the compatible vote clause. -/
theorem period_inv_compat_from (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) :
    ∀ j : ℕ, (∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < j) →
      M.supportCutoff S.C (s + 1) ≤ x.time j → x.time j ≤ T →
      (x.time j ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW) →
      (∀ (k : ℕ) (v : V) (c' : ℕ), k < j → x.lbl k = Event.tick v c' → c' ≤ T) →
      RootsNameBlocksUntil M A x (x.time j) →
      PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ j := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ0 : (0 : ℝ) ≤ (Δ S : ℝ) := Nat.cast_nonneg _
  have hcast : ∀ a b : ℕ, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun a b h => by exact_mod_cast h
  have hvs1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S (s + 1)
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  -- a tick to the clock value `t` is at a step whose real time is in `[t − ΔClockAhead, t + ΔClockBehind]`
  have htw : ∀ (k : ℕ) (v : V) (t : ℕ), x.lbl k = Event.tick v t →
      (t : ℝ) - ΔClockAhead ≤ x.time k ∧ x.time k ≤ t + ΔClockBehind := fun k v t hk =>
    (E.tick_active k v t hk).2
  -- a tick keeps the real time
  have hkeep : ∀ (k : ℕ) (v : V) (t : ℕ), x.lbl k = Event.tick v t → x.time (k + 1) = x.time k :=
    fun k v t hk => R.time_keep k (by rw [hk]; intro h; cases h)
  -- every updater ticks to the cutoff `c`, honest there
  have hupdT : ∀ w ∈ updaterAt M S A x s,
      x.lbl (x.tickStep w (M.supportCutoff S.C (s + 1))) = Event.tick w (M.supportCutoff S.C (s + 1)) ∧
      w ∉ A.corrupted (x.tickStep w (M.supportCutoff S.C (s + 1))) := fun w hw =>
    (tick_honest_of_activeThroughoutToTick M F E) ((updaterAt_window M F) S A s w E hw)
  -- a step whose time is more than `ΔClockBehind` after `c` comes after every updater's tick to `c`
  have hafter : ∀ i : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind < x.time i →
      ∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < i := fun i hi w hw =>
    (lt_of_time_lt M) x R (lt_of_le_of_lt (htw _ _ _ (hupdT w hw).1).2 hi)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hpre hcj0 hjT hjW hTk hR
  have hcT : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ T := le_trans hcj0 hjT
  have hcTN : M.supportCutoff S.C (s + 1) ≤ T := by exact_mod_cast hcT
  -- the invariant at an earlier step of the range
  have IHr : ∀ i : ℕ, i < j → (∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < i) →
      ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time i →
      PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ i := fun i hij h1 h2 =>
    ih i hij h1 h2 (le_trans ((time_mono M) x R hij.le) hjT)
      (hjW.imp_left (le_trans ((time_mono M) x R hij.le)))
      (fun k v c' hk hl => hTk k v c' (lt_trans hk hij) hl)
      (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M ((time_mono M) x R hij.le) hR)
  -- the invariant at a step whose time is more than `ΔClockBehind` after `c` and before `x[j].time`
  have IHt : ∀ i : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind < x.time i → x.time i < x.time j →
      i < j ∧ PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ i := fun i h1 h2 =>
    have hij := (lt_of_time_lt M) x R h2
    ⟨hij, IHr i hij (hafter i h1) (by linarith)⟩
  have PA := (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotesUntil.toAsyncHypsUntil
    M F U R E hNet hSkew hRedeliver) P hcTN
  have hΔn : ΔNet ≤ Δ S := by
    have h : (ΔNet : ℝ) ≤ Δ S := by linarith
    exact_mod_cast h
  have PC := (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotesUntil.toAsyncHypsOfChainBlockUntil M F U) P hΔn
  -- the caches give a finalized block compatible with `B`
  have hFcomp : ∀ n : M.N, CachesCompatibleWith M S B H n → n.finalized.compatible B = true :=
    fun n hn => GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hn.2.2.2.2
      ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2 hn.2.1)
  -- clause 6 at `j`: at a slot `s' ≥ s + 2`, each vote from the invariant at the voter's own tick
  have C6 : ∀ s' : ℕ, s + 1 ≤ s' → (M.supportCutoff S.C s' : ℝ) ≤ x.time j →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s' := by
    intro s' hs' hsct
    rcases Nat.eq_or_lt_of_le hs' with heq | hs2
    · subst heq
      exact (GoldilocksCorrectness.Record.Statements.Executions.votesCompatibleAt_of_votesExtendAt M) S A x
        (P.hHand.2.2.2.2.2.1 Δs b₀ b₁)
    have hvs2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
      (show s + 1 + 1 ≤ s' by omega)
    have hsc' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
    have hsv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S (s' - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s')] at hsv
    have hscm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' - 1)
    have hsctT : M.supportCutoff S.C s' ≤ T := by exact_mod_cast le_trans hsct hjT
    -- the voter's tick to the vote time of `s'` is a step of the range before `j`
    have hvoter : ∀ (u : V) (i : ℕ), x.lbl i = Event.tick u (M.voteTime S.C s') →
        i < j ∧ PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ i ∧
          x.tickStep u (M.voteTime S.C s') = i ∧ u ∉ A.corrupted i ∧
          ((M.voteTime S.C s' : ℕ) : ℝ) - ΔClockAhead ≤ x.time i := fun u i hi => by
      obtain ⟨hlo, hhi⟩ := htw i u _ hi
      have e1 := hcast _ _ (show M.supportCutoff S.C (s + 1) + 3 * Δ S ≤ M.voteTime S.C s' by omega)
      have e2 := hcast _ _ (show M.voteTime S.C s' + Δ S ≤ M.supportCutoff S.C s' by omega)
      push_cast at e1 e2
      obtain ⟨hij, J⟩ := IHt i (by linarith) (by linarith)
      exact ⟨hij, J, (tickStep_eq_of_lbl M) x E hi, E.not_mem_corrupted_of_tick hi, hlo⟩
    -- the support cutoff of `s' − 1` is at or before the voter's tick
    have hprevsc : ∀ i : ℕ, ((M.voteTime S.C s' : ℕ) : ℝ) - ΔClockAhead ≤ x.time i →
        (M.supportCutoff S.C (s' - 1) : ℝ) ≤ x.time i := fun i hi => by
      have e := hcast _ _ (show M.supportCutoff S.C (s' - 1) + 3 * Δ S ≤ M.voteTime S.C s' by omega)
      push_cast at e
      linarith
    refine ⟨fun hk' w hw vote hsend => ?_, fun hgood w hw vote hsend => ?_⟩
    · -- the holders, during the hand-over lock's life
      obtain ⟨i, hi, -⟩ := id hsend
      obtain ⟨hij, ⟨J1, -, J3, J4, -, J6, -⟩, hts, hwi, hlo⟩ := hvoter w i hi
      have hTI : x.tickInput w (M.voteTime S.C s') = x.st i w := by
        unfold Trace.tickInput; rw [hts]
      have hdl := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S hk'
      have hdl2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S (s + S.C.k)
      have hInv : HolderInvAt M S x s B i w := by
        refine J1 w (Finset.mem_inter.1 hw).1 (fun i' hi' => E.not_mem_corrupted_of_le hi' hwi)
          (fun k c' hk hl => ?_) (fun k s'' hk hl => ?_)
        · have h1 := E.clock_mono k i w c' _ hk hwi (Or.inl hl) (Or.inl hi)
          have h2 : c' ≠ M.voteTime S.C s' := fun h => by
            subst h; have := E.tick_unique _ _ w _ hl hi; omega
          omega
        · have h1 := E.clock_mono k i w _ _ hk hwi (Or.inl hl) (Or.inl hi)
          have h2 : M.voteTime S.C s'' ≠ M.voteTime S.C s' := fun h => by
            rw [h] at hl; have := E.tick_unique _ _ w _ hl hi; omega
          have h3 : s'' < s' := by
            by_contra hc'
            have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
              (show s' ≤ s'' by omega)
            omega
          have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
            (show s'' ≤ s' - 1 by omega)
          exact le_trans (hcast _ _ h4) (hprevsc i hlo)
      have hRw : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s'))) := by
        rw [hts]
        exact GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M
          ((time_mono M) x R hij.le) hR
      have hInv' : HolderInvAt M S x s B (x.tickStep w (M.voteTime S.C s')) w := by
        rw [hts]; exact hInv
      have hC : CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C s')) := by
        rw [hTI]; exact J3 w hwi
      have hTwo : ∀ D ∈ (x.tickInput w (M.voteTime S.C s')).tree,
          (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D := by
        rw [hTI]
        exact fun D hD hDh => (blocksTwoPastDescend_at_ofChainBlock M F Fx) S A x i P.hHand.1 J4 w D hwi hD hDh
      have hNC : M.fg_contest (x.tickInput w (M.voteTime S.C s')) = false ∨
          (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s')) := by
        rw [hTI]
        exact (not_contested_or_two_past_of_certificates M F Fx) S A x R E i w hwi J4 (J3 w hwi)
      exact (holder_vote_extends_B_orTwoPast_ofCompat M F U R E hSkew) PA s' w hsctT hRw hs2 hk' hInv' hC
        hTwo hNC (J6 (s' - 1) (by omega) (hprevsc i hlo)) vote hsend
    · -- the honest active voters of a timely slot
      obtain ⟨i, hi, -⟩ := id hsend
      obtain ⟨hij, ⟨-, -, J3, J4, -, J6, -⟩, hts, hwi, hlo⟩ := hvoter w i hi
      have hTI : x.tickInput w (M.voteTime S.C s') = x.st i w := by
        unfold Trace.tickInput; rw [hts]
      have hvtj : ((M.voteTime S.C s' : ℕ) : ℝ) ≤ x.time j := by
        have e := hcast _ _ (show M.voteTime S.C s' ≤ M.supportCutoff S.C s' by omega)
        linarith
      have hRv : RootsNameBlocksUntil M A x
          (max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep w (M.voteTime S.C s')))) :=
        GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M
          (max_le hvtj (by rw [hts]; exact (time_mono M) x R hij.le)) hR
      have hC : CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C s')) := by
        rw [hTI]; exact J3 w hwi
      have hTwo : ∀ D ∈ (x.tickInput w (M.voteTime S.C s')).tree,
          (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D := by
        rw [hTI]; exact fun D hD hDh => (blocksTwoPastDescend_at_ofChainBlock M F Fx) S A x i P.hHand.1 J4 w D
          hwi hD hDh
      have hNC : M.fg_contest (x.tickInput w (M.voteTime S.C s')) = false ∨
          (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s')) := by
        rw [hTI]; exact (not_contested_or_two_past_of_certificates M F Fx) S A x R E i w hwi J4 (J3 w hwi)
      rcases Nat.eq_or_lt_of_le hs2 with heq2 | hs3
      · -- `s' = s + 2`: the previous votes are the hand-over facts'
        subst heq2
        exact (vote_compatible_of_timely_view_ofExtend M F U Fx R E hNet hSkew hRedeliver hΔs) P (s + 1 + 1) w
          hsctT hRv le_rfl hgood hw hC hTwo hNC (fun _ _ => P.hHand.2.2.2.2.2.1 Δs b₀ b₁) vote hsend
      · -- `s' ≥ s + 3`: the previous voters' caches at their own ticks to the vote time of `s' − 1`
        have hCprev : ∀ w' ∈ honestActiveAt M S A x (s' - 1),
            CachesCompatibleWith M S B H (x.tickInput w' (M.voteTime S.C (s' - 1))) := by
          intro w' hw'
          obtain ⟨hl', -⟩ := (tick_honest_of_activeThroughoutToTick M F E)
            ((voteTime_tick_window_of_honestActiveAt M F U) S A x R (s' - 1) w' E hSkew hw')
          obtain ⟨hlo', hhi'⟩ := htw _ w' _ hl'
          have hvs3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
            (show s + 1 + 1 ≤ s' - 1 by omega)
          have e1 := hcast _ _ (show M.supportCutoff S.C (s + 1) + 3 * Δ S ≤ M.voteTime S.C (s' - 1) by omega)
          have e2 := hcast _ _ (show M.voteTime S.C (s' - 1) + 4 * Δ S ≤ M.supportCutoff S.C s' by omega)
          push_cast at e1 e2
          obtain ⟨-, J'⟩ := IHt _ (by linarith) (by linarith)
          unfold Trace.tickInput
          exact J'.2.2.1 w' (E.not_mem_corrupted_of_tick hl')
        exact (vote_compatible_of_timely_view M F U Fx R E hNet hSkew hRedeliver hΔs) P s' w hsctT hRv (by omega)
          hgood hw hC hTwo hNC hCprev (J6 (s' - 1) (by omega) (hprevsc i hlo)) vote hsend
  -- the caches of `w` at a step from `c` on before `j`, honest there: the hand-over facts in the window,
  -- the invariant after it
  have hCw : ∀ (k : ℕ) (w : V), k < j → ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time k → w ∉ A.corrupted k →
      CachesCompatibleWith M S B H (x.st k w) := fun k w hkj h1 hw => by
    by_cases hb : x.time k ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind
    · exact P.hHand.2.2.1 k w h1
        (hjW.elim (fun h => le_trans ((time_mono M) x R hkj.le) h) (fun h => le_trans hb h)) hw
    · push Not at hb
      exact (IHr k hkj (hafter k hb) h1).2.2.1 w hw
  -- each updater's holder invariant, carried from the configuration its tick to `c` leaves to every step up
  -- to `j`, over steps that keep its confirmation state and over its ticks (Lemma 100's step)
  have carry : ∀ w ∈ updaterAt M S A x s, x.HonestThrough A j w →
      (∀ (k c' : ℕ), k < j → x.lbl k = Event.tick w c' → c' < M.voteTime S.C (s + S.C.k + 1)) →
      (∀ (k s' : ℕ), k < j → x.lbl k = Event.tick w (M.voteTime S.C s') → M.supportCutoff S.C s' ≤ T) →
      ∀ n : ℕ, x.tickStep w (M.supportCutoff S.C (s + 1)) + 1 ≤ n → n ≤ j → HolderInvAt M S x s B n w := by
    intro w hw hH ha hb n hn1
    induction n, hn1 using Nat.le_induction with
    | base => exact fun _ => (P.hHand.2.1 w hw).2.2
    | succ n hn ihn =>
      intro hnj
      have hInv := ihn (by omega)
      have hwn1 : w ∉ A.corrupted (n + 1) := hH (n + 1) hnj
      by_cases htk : ∃ c', x.lbl n = Event.tick w c'
      · obtain ⟨c', hl⟩ := htk
        have htn1 : x.time (n + 1) ≤ x.time j := (time_mono M) x R hnj
        have hwn : w ∉ A.corrupted n := E.not_mem_corrupted_of_tick hl
        -- the tick is to a clock value after the hand-over cutoff: `w` ticked to the cutoff at an earlier step
        -- (`clock_mono`, `tick_unique`)
        have hcc : M.supportCutoff S.C (s + 1) ≤ c' :=
          E.clock_mono _ n w _ _ (by omega) hwn (Or.inl (hupdT w hw).1) (Or.inl hl)
        by_cases htn : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time n
        · -- Lemma 100's step at `w`'s tick
          exact (holderInv_step_ofCompat M F U R E hSkew) PA n w (le_trans htn1 hjT)
            (fun s' hl' => hb n s' (by omega) hl')
            (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M htn1 hR)
            (fun c'' hl'' => by rw [hl] at hl''; cases hl''; exact hcc)
            (fun c'' keep hr => by rw [hl] at hr; cases hr)
            (fun c'' hl'' => ha n c'' (by omega) hl'') hInv
            (hCw n w (by omega) htn hwn)
            (fun s' hs' h => C6 s' hs' (le_trans h htn1))
        · -- a tick at a real time before the hand-over cutoff, to a clock value in `(c, c + Δ S)`: nothing is
          -- due there but the expiry
          push Not at htn
          have hne : c' ≠ M.supportCutoff S.C (s + 1) := fun h => by
            subst h
            have := E.tick_unique _ _ w _ hl (hupdT w hw).1
            omega
          have hhi : c' < M.supportCutoff S.C (s + 1) + Δ S := by
            have h1 := (htw n w c' hl).1
            have h2 : (c' : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by push_cast; linarith
            exact_mod_cast h2
          exact (holderInv_step_idle_tick M F U R E) n w c' hl
            ((not_duty_of_cutoff_lt_lt M F U) s c' (lt_of_le_of_ne hcc (Ne.symm hne)) hhi)
            (ha n c' (by omega) hl) hInv
      · push Not at htk
        exact (holderInv_of_keepsConfirmation M F U R E) (Nat.le_succ n) hwn1
          (keepsConfirmation_of_no_tick_between M F x R w (Nat.le_succ n) (fun i h1 h2 t' => by
            obtain rfl : i = n := by omega
            exact htk t')) hInv
  -- clause 1 at `j`
  have C1 : ∀ w ∈ updaterAt M S A x s, x.HonestThrough A j w →
      (∀ (k c' : ℕ), k < j → x.lbl k = Event.tick w c' → c' < M.voteTime S.C (s + S.C.k + 1)) →
      (∀ (k s' : ℕ), k < j → x.lbl k = Event.tick w (M.voteTime S.C s') → M.supportCutoff S.C s' ≤ x.time j) →
      HolderInvAt M S x s B j w := fun w hw hH ha hb =>
    carry w hw hH ha (fun k s' hk hl => by exact_mod_cast le_trans (hb k s' hk hl) hjT) j (hpre w hw) le_rfl
  -- outside the window, the step before `j` is in the range
  have hprev : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind < x.time j →
      ∃ j' : ℕ, j = j' + 1 ∧ PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ j' := fun hnb => by
    obtain ⟨j₀, hj₀1, hj₀2⟩ := hWin
    have hj₀j : j₀ < j := (lt_of_time_lt M) x R (lt_of_le_of_lt hj₀2 hnb)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    refine ⟨j', rfl, IHr j' (Nat.lt_succ_self j') (fun w hw => ?_)
      (le_trans hj₀1 ((time_mono M) x R (by omega)))⟩
    obtain ⟨hl, -⟩ := hupdT w hw
    have h1 := (htw _ _ _ hl).2
    have h2 : x.tickStep w (M.supportCutoff S.C (s + 1)) < j' + 1 := (lt_of_time_lt M) x R (by linarith)
    rcases Nat.lt_or_ge (x.tickStep w (M.supportCutoff S.C (s + 1))) j' with h | h
    · exact h
    · exfalso
      obtain rfl : x.tickStep w (M.supportCutoff S.C (s + 1)) = j' := by omega
      have := hkeep _ _ _ hl
      linarith
  -- a tick at the step before `j` is to a clock value at most `T`
  have hTt : ∀ j' : ℕ, j = j' + 1 → ∀ (v : V) (c' : ℕ), x.lbl j' = Event.tick v c' → c' ≤ T :=
    fun j' hj' v c' hl => hTk j' v c' (by omega) hl
  -- clauses 3, 4 and 5 at `j`: the hand-over facts in the window, the steps after it
  have C345 : (∀ u : V, u ∉ A.corrupted j → CachesCompatibleWith M S B H (x.st j u)) ∧
      CertificatesCompatibleWithAtOfChainBlock M A x H B j ∧
      AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j := by
    by_cases hbase : x.time j ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind
    · have hbW : x.time j ≤ tW := hjW.elim id (fun h => le_trans hbase h)
      exact ⟨fun u hu => P.hHand.2.2.1 j u hcj0 hbW hu, P.hHand.2.2.2.1 j hcj0 hbW,
        P.hHand.2.2.2.2.1 j hcj0 hbW⟩
    push Not at hbase
    obtain ⟨j', rfl, -, -, I3, -, I5, I6, -⟩ := hprev hbase
    have C5 := (attestations_step_ofHeldEntry_ofCompat M F U R E hNet hSkew hRedeliver) PC j'
      (hTt j' rfl) hWin (hjW.elim (fun h => by linarith) id) hR I5 I6
    have C4 := (certificatesCompatibleWithAtOfChainBlock_of_attestations M F) S A x R E (j' + 1) hR
      (P.hAdvQ.mono (max_le hjT (by have := P.ht₀; exact_mod_cast (show t₀ ≤ T by omega)))) C5
    exact ⟨fun u hu => (caches_step_ofChainBlock M F Fx) S A x R E j' u hu
      (I3 u (E.not_mem_corrupted_of_le (Nat.le_succ j') hu)) C4, C4, C5⟩
  -- clause 7 at `j`: the invariant at the validator's tick to the support cutoff of `s' + 1`
  have C7 : ∀ s' : ℕ, s + 1 ≤ s' → VotesDueByCutoff M S Δs b₀ b₁ s' →
      ∀ v ∈ honestActiveAt M S A x s', x.tickStep v (M.supportCutoff S.C (s' + 1)) < j → ∀ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
        C'.compatible B = true := by
    intro s' hs' hdue v hv hkvj C' hC'
    have hsc' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
    have hsc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
    have hvs' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S s'
    have hvs2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
      (show s + 1 ≤ s' by omega)
    obtain ⟨kv, hkv, -⟩ := GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_awakeThroughoutToTick.1
      (Finset.mem_sdiff.1 hv).1
    obtain ⟨hlo, -⟩ := htw _ v _ hkv
    have e1 := hcast _ _ (show M.supportCutoff S.C (s + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s' + 1) by omega)
    push_cast at e1
    -- `v`'s tick to the support cutoff of `s' + 1` is the step `kv`, before `j`
    rw [(tickStep_eq_of_lbl M) x E hkv] at hkvj
    have hkvt : x.time kv ≤ x.time j := (time_mono M) x R hkvj.le
    -- the support cutoff of `s'` is `4 * Δ S` before that of `s' + 1`, so before the tick's real time
    have hscs : (M.supportCutoff S.C s' : ℝ) ≤ x.time j := by
      have e := hcast _ _ (show M.supportCutoff S.C s' + 4 * Δ S ≤ M.supportCutoff S.C (s' + 1) by omega)
      push_cast at e
      linarith
    obtain ⟨-, -, J3, -⟩ := IHr kv hkvj (hafter kv (by linarith)) (by linarith)
    have hTI : x.tickInput v (M.supportCutoff S.C (s' + 1)) = x.st kv v := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkv]
    exact (confirmation_compatible_of_timely_votes M F U R E hNet hSkew hRedeliver hΔs) P s' v
      (hTk kv v _ hkvj hkv)
      (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M
        (R.time_mono (le_trans ((tickStep_cut_lt_succ_of_updater M F U) x R E hΔs hSkew
          (GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_activeThroughoutToTick_of_le
        ((duty_window_start_le_of_le M F U) S (Nat.le_succ s')) ((honestActiveAt_window M F) S A s' v E hv))).le
          (by rw [(tickStep_eq_of_lbl M) x E hkv]; exact hkvj.le))) hR)
      hs' hdue hv (by rw [hTI]; exact hFcomp _ (J3 v (E.not_mem_corrupted_of_tick hkv)))
      (C6 s' hs' hscs) C' hC'
  -- clause 2 at `j`
  have C2 : ∀ w ∈ updaterAt M S A x s, x.HonestThrough A j w →
      B.AncestorEq (x.st j w).latestConfirmed ∧ (x.st j w).latestConfirmed ∈ (x.st j w).tree := by
    intro w hw hH
    refine ⟨?_, (latest_confirmed_mem_T_of_exec M F U) x R E j w⟩
    by_cases hab : (∀ (k c' : ℕ), k < j → x.lbl k = Event.tick w c' → c' < M.voteTime S.C (s + S.C.k + 1)) ∧
        (∀ (k s' : ℕ), k < j → x.lbl k = Event.tick w (M.voteTime S.C s') → M.supportCutoff S.C s' ≤ T)
    · exact (carry w hw hH hab.1 hab.2 j (hpre w hw) le_rfl).2.1
    -- in the window both hold, so `j` is after it
    have hnb : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind < x.time j := by
      by_contra hle
      push Not at hle
      apply hab
      have hdl2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
        (show s + 1 + 1 ≤ s + S.C.k + 1 by omega)
      refine ⟨fun k c' hk hl => ?_, fun k s' hk hl => ?_⟩
      · obtain ⟨hlo, -⟩ := htw _ _ _ hl
        have htk : x.time k ≤ x.time j := (time_mono M) x R hk.le
        have h1 : (c' : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by push_cast; linarith
        have h2 : c' < M.supportCutoff S.C (s + 1) + Δ S := by exact_mod_cast h1
        omega
      · obtain ⟨hlo, -⟩ := htw _ _ _ hl
        have htk : x.time k ≤ x.time j := (time_mono M) x R hk.le
        have h1 : ((M.voteTime S.C s' : ℕ) : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by
          push_cast; linarith
        have h2 : M.voteTime S.C s' < M.supportCutoff S.C (s + 1) + Δ S := by exact_mod_cast h1
        have h3 : s' ≤ s + 1 := by
          by_contra hc'
          have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
            (show s + 1 + 1 ≤ s' by omega)
          omega
        exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h3)
          hcTN
    obtain ⟨j', rfl, -, I2, I3, -, -, -, -⟩ := hprev hnb
    have hHj : x.HonestThrough A j' w := fun i' hi' => hH i' (le_trans hi' (Nat.le_succ j'))
    obtain ⟨hB2, hT2⟩ := I2 w hw hHj
    -- the step keeps the record, or it is `w`'s confirmation update at the support cutoff of the slot
    -- of its clock value (`step_cases_latest`, the record's form)
    rcases (step_cases_latest M F) x R E j' w with h | ⟨t, hl, -, ht, ⟨τ, hτ, hτle⟩, hcu⟩
    · rw [h]
      exact hB2
    obtain ⟨hlo, -⟩ := htw _ _ _ hl
    have hk1 := hkeep _ _ _ hl
    have htT : t ≤ T := hTt j' rfl w t hl
    have hTI : x.tickInput w t = x.st j' w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hTI] at hcu hτ
    -- the spec's slot of `t` is the layout's
    have hsl : S.C.slot (t : Int) = M.slot S.C t := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    rw [hsl] at ht hτle hcu
    have hst := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot_eq M.toSlotLayout F.sched U) S ht
    have hs0 : M.slot S.C t ≠ 0 := by
      intro h0
      rw [h0] at hst
      have e0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S 0
      have e1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
        (Nat.zero_le s)
      have e2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S s
      -- the update to the cutoff of slot `0` is to a clock value before `c`, after `w`'s tick to `c`
      obtain ⟨hlc, -⟩ := hupdT w hw
      have hlt : x.tickStep w (M.supportCutoff S.C (s + 1)) < j' := by
        rcases Nat.lt_or_ge (x.tickStep w (M.supportCutoff S.C (s + 1))) j' with h | h
        · exact h
        · exfalso
          have h' := hpre w hw
          obtain rfl : x.tickStep w (M.supportCutoff S.C (s + 1)) = j' := by omega
          rw [hlc] at hl
          injection hl with h1 h2
          omega
      have := E.clock_mono _ _ w _ _ hlt (hH j' (Nat.le_succ j')) (Or.inl hlc) (Or.inl hl)
      omega
    obtain ⟨s'', hs''⟩ : ∃ s'', M.slot S.C t = s'' + 1 := ⟨M.slot S.C t - 1, by omega⟩
    rw [hs''] at hst hτle hcu
    by_cases hd : t < M.voteTime S.C (s + S.C.k + 1)
    · -- before the lock's deadline the carry's two conditions hold at `j`: every tick of `w` before `j` is to a
      -- clock value at most `t` (`clock_mono`; the tick at `j'` is `w`'s update to `t`), so before the deadline,
      -- and a tick to the vote time of a slot `s'` has `s' ≤ s'' + 1`, whose support cutoff is at most `t ≤ T`
      --
      exfalso
      apply hab
      have hle : ∀ (k c' : ℕ), k < j' + 1 → x.lbl k = Event.tick w c' → c' ≤ t := by
        intro k c' hk hlk
        rcases Nat.lt_or_ge k j' with hk' | hk'
        · exact E.clock_mono k j' w c' t hk' (hH j' (Nat.le_succ j')) (Or.inl hlk) (Or.inl hl)
        · obtain rfl : k = j' := by omega
          rw [hl] at hlk
          cases hlk
          exact le_rfl
      refine ⟨fun k c' hk hlk => lt_of_le_of_lt (hle k c' hk hlk) hd, fun k s' hk hlk => ?_⟩
      have h1 := hle k _ hk hlk
      have e1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S (s'' + 1)
      have e2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s'' + 1)
      have h2 : s' ≤ s'' + 1 := by
        by_contra hc'
        have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S
          (show s'' + 1 + 1 ≤ s' by omega)
        omega
      exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2)
        (by omega)
    have hdead : s + S.C.k ≤ s'' :=
      (GoldilocksCorrectness.Record.Proofs.Routines.slot_of_update_after_deadline M.toSlotLayout F.sched) S s s''
        (by rw [hst]; omega)
    -- the three cases of the record after the update (the record's form)
    rcases GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_cases
        (Nat.succ_ne_zero s'') hcu with
      ⟨-, hkeep'⟩ | ⟨C', hsave, ⟨-, hkeep'⟩ | ⟨-, hadv⟩⟩
    · rw [hkeep']
      exact hB2
    · rw [hkeep']
      exact hB2
    rw [hadv]
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.advance_some F) (M.fg_to_ac (x.st j' w))
        (x.st j' w).latestConfirmed C' with ⟨-, -, ha⟩ | ⟨hn, ha⟩
    · rw [ha]
      exact hB2
    rw [ha]
    rw [Nat.succ_sub_one] at hsave
    have hl' : x.lbl j' = Event.tick w (M.supportCutoff S.C (s'' + 1)) := by rw [hst]; exact hl
    have hτ' : (x.tickInput w (M.supportCutoff S.C (s'' + 1))).awakeSince = some τ := by
      rw [hst, hTI]; exact hτ
    have hupd : w ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' + 1))
        (M.supportCutoff S.C (s'' + 1)) :=
      (updaterAt_of_update_tick M F U R) E j' s'' w τ hl' hτ' hτle
    have hsaved : (x.tickOutput w (M.supportCutoff S.C (s'' + 1))).savedConfirmation s'' = some C' := by
      unfold Trace.tickOutput
      rw [(tickStep_eq_of_lbl M) x E hl']
      exact hsave
    have hsc'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s'' + 1)
    have hsc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s''
    have hvs'' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S s''
    have hwj : w ∉ A.corrupted j' := hHj _ le_rfl
    have hFst : (x.tickInput w (M.supportCutoff S.C (s'' + 1))).finalized.compatible B = true := by
      rw [hst, hTI]
      exact hFcomp _ (I3 w hwj)
    have hscR : (M.supportCutoff S.C s'' : ℝ) ≤ x.time (j' + 1) := by
      have e := hcast _ _ (show M.supportCutoff S.C s'' + 4 * Δ S ≤ t by omega)
      push_cast at e
      linarith
    have hCB := (confirmation_compatible_of_updater M F U R E hNet hSkew hRedeliver hΔs) P s'' w (by omega)
      (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M
        (R.time_mono (le_trans ((tickStep_cut_lt_succ_of_updater M F U) x R E hΔs hSkew hupd).le
          (by rw [(tickStep_eq_of_lbl M) x E hl']; exact Nat.le_succ j'))) hR) (by omega)
      (Or.inr ((votes_due_of_after_period_max M F U) S P.hb₁ hdead)) hupd hFst
      (C6 s'' (by omega) hscR) C' hsaved
    rcases (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 hCB with hC'B | hBC'
    · -- `C'` an ancestor of `B`: `B` an ancestor of the finalized block, or the record kept
      rcases (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 (hFcomp _ (I3 w hwj)) with
        hFB | hBF
      · exfalso
        exact hn ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hT2,
          GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFB hB2⟩,
          GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hC'B hB2⟩
      · -- the saved confirmation descends from the finalized block (the record's form)
        have hFC := GoldilocksCorrectness.Record.Statements.Routines.saved_confirmation_F_ancestorEq
          (Nat.le_add_left 1 s'') hcu
        rw [Nat.add_sub_cancel, (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)] at hFC
        exact GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hBF (hFC C' hsave)
    · exact hBC'
  obtain ⟨C3, C4, C5⟩ := C345
  exact ⟨fun w hw hH ha hb => C1 w hw hH ha hb, C2, C3, C4, C5, fun s' hs' hvt => C6 s' hs' hvt, C7⟩

/-- **Statement 3′: the joint invariant under the compatible vote clause, for ever.** The proof; the
audited statement is in `Statements/Executions/PeriodInductionCompatStatements.lean`. Over the steps after every
updater's tick to the hand-over cutoff `c` and at a time at least `c`, it is
`period_inv_compat_from`.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses.
- `T`: the time up to which `P`'s premises are read;
  the invariant is concluded at the steps whose time is at most `T`.

Read aloud: the hand-over facts carry for ever in the weakened form: at every step after the
hand-over update, given that roots name blocks by that step's time, the seven clauses hold, with
votes and confirmations compatible with `B`. -/
theorem period_inv_compat_all (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) :
    ∀ j : ℕ, (∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < j) →
      M.supportCutoff S.C (s + 1) ≤ x.time j → x.time j ≤ T →
      (∀ (k : ℕ) (v : V) (c' : ℕ), k < j → x.lbl k = Event.tick v c' → c' ≤ T) →
      RootsNameBlocksUntil M A x (x.time j) →
      PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ j := by
  intro j h1 h2 h3
  exact period_inv_compat_from M F U Fx R E hNet hSkew hRedeliver hΔs P hWin j h1 h2 h3 (Or.inr le_rfl)

/-- **Lemma 104′: from slot `s + k + 1` on, the honest votes and confirmations do not conflict
with `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`. The invariant in the form after every
updater's tick (`period_inv_compat_from`) at a member `v`'s own tick to the support cutoff `c'` of
`s' + 1`: that tick is at a real time at least `c' − ΔClockAhead`, after every updater's
tick to the hand-over cutoff `c` (at most `c + ΔClockBehind`, with `c + 4Δ ≤ c'` and
`ΔClockAhead + ΔClockBehind < Δ`), and `hR` names the roots up to it. Its sixth clause at `s'` (with no
member, both conjuncts of `VotesCompatibleAt` are vacuous at `s' ≥ s + k + 1`); its third clause for
`v`'s finalized block at that tick's input, and statement 2′ at `s'`, whose votes are due by its
cutoff (`b₁ ≤ M.voteTime S.C s'`).

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses.

Read aloud: from slot `s + k + 1` on, every honest active vote is on `B`'s chain or comes from a
voter justified past `B` and does not conflict with `B`, and no honest confirmation conflicts with
`B`. -/
theorem after_period_compat (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) :
    ∀ s' : ℕ, s + S.C.k + 1 ≤ s' →
      (∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s' + 1)) →
        RootsNameBlocksUntil M A x (x.time k)) →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s' ∧
      ∀ v ∈ honestActiveAt M S A x s', ∀ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
        C'.compatible B = true := by
  intro s' hs' hR
  have hΔ0 : (0 : ℝ) ≤ Δ S := Nat.cast_nonneg _
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hcs : M.supportCutoff S.C (s + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s' + 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s + 1 + 1 ≤ s' + 1 by omega)
    omega
  have hcs' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S s'
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + 4 * Δ S ≤ (M.supportCutoff S.C (s' + 1) : ℕ) := by
    exact_mod_cast hcs
  have hcR' : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s' : ℕ) + 4 * Δ S := by
    exact_mod_cast hcs'
  -- statement 3′ in the form after every updater's tick (`period_inv_compat_from`) at a member's own tick to the
  -- support cutoff of `s' + 1`: that tick is at a real time at least `c' − ΔClockAhead`, after every updater's tick to
  -- the hand-over cutoff `c` (at a real time at most `c + ΔClockBehind`, and `c + 4Δ ≤ c'`), and the roots come from
  -- `hR` at that tick
  have hInvAt : ∀ v ∈ honestActiveAt M S A x s',
      x.lbl (x.tickStep v (M.supportCutoff S.C (s' + 1))) = Event.tick v (M.supportCutoff S.C (s' + 1)) ∧
      v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s' + 1))) ∧
      ((M.supportCutoff S.C s' : ℕ) : ℝ) ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))) ∧
      PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ (x.tickStep v (M.supportCutoff S.C (s' + 1))) := by
    intro v hv
    obtain ⟨hl, hvh⟩ := (tick_honest_of_activeThroughoutToTick M F) E ((honestActiveAt_window M F) S A s' v E hv)
    have ht := ((time_of_lbl_tick M) x R E hl).1
    obtain ⟨T, hT⟩ := exists_nat_ge (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))) + ΔClockAhead)
    have hA0 := E.ahead_nonneg
    have hticks : ∀ w ∈ updaterAt M S A x s,
        x.tickStep w (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.supportCutoff S.C (s' + 1)) := by
      intro w hw
      obtain ⟨hlw, -⟩ := (tick_honest_of_activeThroughoutToTick M F) E ((updaterAt_window M F) S A s w E hw)
      have htw := ((time_of_lbl_tick M) x R E hlw).1
      exact (lt_of_time_lt M) x R (by linarith)
    exact ⟨hl, hvh, by linarith, (period_inv_compat_from M F U Fx R E hNet hSkew hRedeliver hΔs)
      ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P T) hWin _
      hticks (by linarith) (by linarith) (Or.inr le_rfl)
      (fun k u c' hk hlk => (tick_clock_le_of_time_le M F) E hT k u c' ((time_mono M) x R hk.le) hlk) (hR _ v hl)⟩
  -- the sixth clause at a member's tick; with no member, both conjuncts of `VotesCompatibleAt` are vacuous
  have hVC : VotesCompatibleAt M S A x s B Δs b₀ b₁ s' := by
    by_cases hne : ∃ v, v ∈ honestActiveAt M S A x s'
    · obtain ⟨v, hv⟩ := hne
      obtain ⟨-, -, hcs'', I⟩ := hInvAt v hv
      exact I.2.2.2.2.2.1 s' (by omega) hcs''
    · exact ⟨fun h => absurd h (by omega), fun _ u hu => (hne ⟨u, hu⟩).elim⟩
  refine ⟨hVC, fun v hv C' hC' => ?_⟩
  -- the third clause at `v`'s own tick gives its finalized block at that tick's input; statement 2′
  obtain ⟨hl, hvh, hcs'', I⟩ := hInvAt v hv
  have hn := I.2.2.1 v hvh
  have hF : (x.tickInput v (M.supportCutoff S.C (s' + 1))).finalized.compatible B = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hn.2.2.2.2
      ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2 hn.2.1)
  exact (confirmation_compatible_of_timely_votes M F U R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P
      (M.supportCutoff S.C (s' + 1))) s' v le_rfl
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M
      (R.time_mono ((tickStep_cut_lt_succ_of_updater M F U) x R E hΔs hSkew
        (GoldilocksCorrectness.Statements.AbstractTrace.Activity.mem_activeThroughoutToTick_of_le
          ((duty_window_start_le_of_le M F U) S (Nat.le_succ s')) ((honestActiveAt_window M F) S A s' v E hv))).le) (hR _ v hl)) (by omega)
    (Or.inr (votes_due_of_after_period_max M F U S P.hb₁ (by omega))) hv hF hVC C' hC'

/-- The certificate clause at every step: some later step `j₀` comes after every updater's tick to the
hand-over cutoff at a real time at least that cutoff (`exists_step_after_ticks`, T-RC43-1); the invariant
in the form after every updater's tick (`period_inv_compat_from`) holds at `j₀`, its attestation clause
covers every attestation sent before the given step (fewer attestations), and the certificate step
concludes the clause there.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses; `hRoots`: roots name blocks; `j`: the step.

Read aloud: at every step, no honest validator holds a chain with a certificate at a height greater
than `H` for a block conflicting with `B`. -/
theorem certificatesCompatibleWithAtOfChainBlock_all (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (hRoots : RootsNameBlocks M A x) (j : ℕ) :
    CertificatesCompatibleWithAtOfChainBlock M A x H B j := by
  have hR := fun t => (rootsNameBlocksUntil_of_rootsNameBlocks M) x F R E t hRoots
  -- a step `j₀` after `j`, after every tick to the hand-over cutoff `c`, at a real time at least `c` (T-RC43-1)
  obtain ⟨j₀, hjj₀, hticks, hcj₀⟩ := (exists_step_after_ticks M F) R E j (M.supportCutoff S.C (s + 1))
  have hupd : ∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < j₀ := by
    intro w hw
    exact hticks _ w ((tick_honest_of_activeThroughoutToTick M F) E ((updaterAt_window M F) S A s w E hw)).1
  -- statement 3′ in the form after every updater's tick, at `j₀`: its attestation clause covers every
  -- attestation sent before `j`
  obtain ⟨T, hT⟩ := exists_nat_ge (x.time j₀ + ΔClockAhead)
  have hA0 := E.ahead_nonneg
  have hT0 : x.time j₀ ≤ T := by linarith
  have hInv := (period_inv_compat_from M F U Fx R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P T) hWin j₀
    hupd hcj₀ hT0 (Or.inr le_rfl) (fun k u c' hk hlk => (tick_clock_le_of_time_le M F) E hT k u c' ((time_mono M) x R hk.le) hlk)
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M hT0 (hR T))
  obtain ⟨T', hT'⟩ := exists_nat_ge (max (x.time j) (t₀ : ℝ))
  refine (certificatesCompatibleWithAtOfChainBlock_of_attestations M F) S A x R E (t₀ := t₀) j
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M (le_trans (le_max_left _ _) hT')
      (hR T')) ((P.hAdvQ T').mono hT') ?_
  intro i t v a hi hl hsent
  exact hInv.2.2.2.2.1 i t v a (lt_trans hi hjj₀) hl hsent

/-- **The certificate corollary.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses; `hRoots`: roots name blocks.

Read aloud: no honest validator ever holds a chain with a certificate at a height greater than `H`
for a block of that chain conflicting with `B`. -/
theorem certificates_compatible_with_ofChainBlock (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (hRoots : RootsNameBlocks M A x) :
    CertificatesCompatibleWithOfChainBlock M A x H B :=
  fun j => (certificatesCompatibleWithAtOfChainBlock_all M F U Fx R E hNet hSkew hRedeliver hΔs) P hWin hRoots j

/-- **The two-past corollary.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`. `blocksTwoPastDescend_at_ofChainBlock`
at every step, with the certificate clause there.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses; `hRoots`: roots name blocks.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
theorem blocks_two_past_descend (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (hRoots : RootsNameBlocks M A x) :
    BlocksTwoPastDescend M S A x B :=
  fun j => (blocksTwoPastDescend_at_ofChainBlock M F Fx) S A x j P.hHand.1
    ((certificatesCompatibleWithAtOfChainBlock_all M F U Fx R E hNet hSkew hRedeliver hΔs) P hWin hRoots j)

end GoldilocksCorrectness.Record.Proofs.Executions

