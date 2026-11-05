module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FrameStatementsFGState
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.SelectionKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseKit, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PhaseKit.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the kit of the phase, an honest Goldfish
vote names a block on the chain of its voter's fork-choice root, the only slot-`s` block an honest
validator holds is the honest proposer's, every frame of a node state has a viable head, a lock at
the justified height of a state in box 2 is on its justified block, the counting hypotheses of a
round from a committee majority, `head_height_floor` ordered by delivery, and the restrictions of
the round's members and of the chain invariant. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_cast slotStart_eq supportCutoff_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_witness_keeps fg_on_block_eq
  fg_on_block_witnessed head_height_floor_initial)

open GoldilocksCorrectness.Proofs.Routines (WitnessedFrom on_attestation_witness_keeps
  on_block_witnessedFrom tick_block_unique tick_witnessedFrom witnessedFrom_of_frame
  witnessedFrom_refl witnessedFrom_trans)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_witnessedFrom)

open GoldilocksCorrectness.Proofs.Routines (supportCutoff_mono)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)



open GoldilocksCorrectness.Record.Statements.Routines (hMax)
open GoldilocksCorrectness.Record.Proofs.Routines (CachesWitnessed)

open GoldilocksCorrectness.Record.Statements.Routines (BoxTwo ChainStatesComputed CountedVotes
  HeightCacheBounds)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject author)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq mem_voter_block_tree_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The restriction facts -/

/-- A later round's members are among an earlier round's, and the validators honest at a later
time are among every round's. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `s'' ≤ s'''`: the two slots; `tAwakeEnd`: the time.
- `R`: the run's facts (the time moves by at most one per step and never back).

Read aloud: a later round's members are among an earlier round's, and the phase set is among every
round's. -/
theorem roundMembers_mono (S : Setup V) (A : Activity V) (s'' s''' tAwakeEnd : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (h : s'' ≤ s''')
    (hEnd : M.supportCutoff S.C s''' ≤ tAwakeEnd) :
    roundMembers M S A x s''' ⊆ roundMembers M S A x s'' ∧
      Finset.univ \ A.corruptedAtTime x tAwakeEnd ⊆ roundMembers M S A x s''' := by
  have hle : M.supportCutoff S.C s'' ≤ M.supportCutoff S.C s''' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hback : ∀ {t t' : ℕ} {v : V}, t ≤ t' → v ∉ A.corruptedAtTime x t' →
      v ∉ A.corruptedAtTime x t := by
    -- the time moves by at most one per step and never back (`R`)
    intro t t' v h hv
    exact (not_mem_corruptedAtTime_of_le M) x R E h hv
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact hback hle hv
  · simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact hback hEnd hv

/-- `HonestChainExtends` restricts to a subset of the members. The proof; the audited statement
is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon`: the two sets;
  `B`: the block; `s'`: the slot.

Read aloud: `HonestChainExtends` restricts to a subset of the members. -/
theorem honestChainExtends_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon Hon' : Finset V) (B : Block V) (s' : ℕ)
    (hSub : Hon' ⊆ Hon) (hInv : HonestChainExtends M S A x Hon B s') :
    HonestChainExtends M S A x Hon' B s' :=
  ⟨fun u hu => hInv.1 u (hSub hu), fun w hw => hInv.2.1 w (hSub hw),
    fun v hv => hInv.2.2 v (hSub hv)⟩

/-- The chain invariant restricts to a subset of the members. The proof; the audited statement
is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon`: the two sets;
  `𝓒`: the family; `s'`: the slot.

Read aloud: the chain invariant restricts to a subset of the members. -/
theorem chainInvFor_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon Hon' : Finset V) (𝓒 : Block V → Prop) (s' : ℕ)
    (hSub : Hon' ⊆ Hon) (hInv : ChainInvFor M S A x Hon 𝓒 s') :
    ChainInvFor M S A x Hon' 𝓒 s' :=
  fun C hC => (honestChainExtends_mono M F) S A x Hon Hon' C s' hSub (hInv C hC)

/-! ## The counting hypotheses -/

/-- The counting hypotheses of a round from a committee majority in `Hon`, on the node state at a step `i`. The proof; the audited
statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `i`: the step;
  `Hon`: the validators; `v`: the validator whose state is read.

Read aloud: a committee majority in `Hon` bounds the committee, the pool and the counted votes of
the slot by twice the committee's members in `Hon`. -/
theorem counting_of_committee_majority_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s i : ℕ) (Hon : Finset V) (v : V)
    (hMaj : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card) :
    (S.P.committee s).card ≤ 2 * (S.P.committee s ∩ Hon).card ∧
    M.voters_count (M.votesHeldSet (x.st i v) s) < 2 * (S.P.committee s ∩ Hon).card ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.st i v) (s + 1)
        votes support_votes →
      M.voters_count votes < 2 * (S.P.committee s ∩ Hon).card) := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left (s₁ := S.P.committee s) (s₂ := Hon))
  have hMaj' : (S.P.committee s \ (S.P.committee s ∩ Hon)).card <
      (S.P.committee s ∩ Hon).card := by omega
  refine ⟨Nat.le_of_lt hMaj, ?_, ?_⟩
  · exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F) ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E i v s)
      hMaj'
  · intro votes support_votes hC
    exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((countedVotes_committee_st M F) S A x R E i s v votes support_votes hC) hMaj'

/-- The counting hypotheses of a round from a committee majority in `Hon`. The proof; the audited
statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `t`: the time;
  `Hon`: the validators; `v`: the validator whose state is read.

Read aloud: a committee majority in `Hon` bounds the committee, the pool and the counted votes of
the slot by twice the committee's members in `Hon`. -/
theorem counting_of_committee_majority (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s t : ℕ) (Hon : Finset V) (v : V)
    (hMaj : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card) :
    (S.P.committee s).card ≤ 2 * (S.P.committee s ∩ Hon).card ∧
    M.voters_count (M.votesHeldSet (x.stateBefore t v) s) < 2 * (S.P.committee s ∩ Hon).card ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.stateBefore t v) (s + 1)
        votes support_votes →
      M.voters_count votes < 2 * (S.P.committee s ∩ Hon).card) := by
  exact (counting_of_committee_majority_st M F) S A x R E s (x.stepBefore t) Hon v hMaj

/-! ## The committee majority and the members of a slot -/

omit [RootOrder] in
/-- From committee sleepiness at slot `s + 1`, more than half of the committee of slot `s` is
among the validators honest at the support cutoff of slot `s + 1`. The proof; the audited
statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which committee sleepiness
  holds; `s`: the slot; `T`: the time up to which committee sleepiness is read (the update of slot
  `s`, `M.supportCutoff S.C (s + 1)`, is at most `T`).

Read aloud: from committee sleepiness read up to a time no earlier than the update of slot `s`, the
committee of slot `s` has a majority among the validators honest at the update of slot `s`. -/
theorem committee_majority_of_committeeSleepiness (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (anchor s : ℕ) {T : ℕ} (hSleepK : CommitteeSleepinessUntil M S A x anchor T)
    (hs : anchor ≤ M.slotStart S.C (s + 1)) (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    (S.P.committee s).card < 2 * (S.P.committee s ∩ roundMembers M S A x (s + 1)).card := by
  have hK := hSleepK (s + 1) (by omega) hs hT
  rw [Nat.add_sub_cancel, Finset.inter_comm] at hK
  have hsplit := Finset.card_sdiff_add_card_inter (S.P.committee s) (honestActiveAt M S A x s)
  have hsub : S.P.committee s ∩ honestActiveAt M S A x s ⊆
      S.P.committee s ∩ roundMembers M S A x (s + 1) := by
    refine Finset.inter_subset_inter (subset_refl _) (fun v hv => ?_)
    simp only [honestActiveAt, roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or] at hv ⊢
    exact hv.2.1
  have hle := Finset.card_le_card hsub
  omega

/-- In the phase, the validators honest at the support cutoff of slot `s + 1` are honest active
at slot `s`, and those honest at the support cutoff of slot `s + 2` are among them. The proof;
the audited statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `tGAT`, `tAwakeEnd`: the ends of the interval in which
  every honest validator is awake; `s`: the slot.
- `R`: the run's facts (the time moves by at most one per step and never back).

Read aloud: in the phase, every validator honest at the slot's update is awake through the slot's
duties and honest at its update, and the next slot's members are among this slot's. -/
theorem roundMembers_subset_honestActiveAt (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (tGAT tAwakeEnd s : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hsw : tGAT ≤ M.dutyWindowStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    roundMembers M S A x (s + 1) ⊆ honestActiveAt M S A x s ∧
    roundMembers M S A x (s + 2) ⊆ roundMembers M S A x (s + 1) := by
  refine ⟨fun v hv => (hActive s hsw hEnd v (Finset.mem_sdiff.1 hv).2).1, fun v hv => ?_⟩
  refine Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun hc => (Finset.mem_sdiff.1 hv).2 ?_⟩
  obtain ⟨i, hi, hci⟩ := Activity.mem_corruptedAtTime.1 hc
  have hmono : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s + 2) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  exact Activity.mem_corruptedAtTime.2 ⟨i, le_trans hi (by exact_mod_cast hmono), hci⟩

/-! ## The only block of a slot -/

/-- The only slot-`s` block an honest validator holds is the honest proposer's. The proof; the
audited statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `s`: the slot;
  `t`: the time; `B`: the proposal; `B₁`: the held block; `p`: the proposer; `w`: the holder.

Read aloud: the only slot-`s` block a validator holds before `t` is the honest proposer's. -/
theorem only_block_of_unforgeability (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s t : ℕ) (B B₁ : Block V)
    (p w : V)
    (hp : A.HonestThroughTime x t p) (hps : S.P.proposer s = p)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₁ : B₁ ∈ (x.stateBefore t w).tree) (hslot : B₁.slot = s) :
    B₁ = B := by
  obtain ⟨iB, hlB, hmB⟩ := hPropose
  -- the slot is positive: a tick runs at a time at least `1`
  have hs0 : s ≠ 0 := by
    obtain ⟨-, n0, sent0, hrun0, hmem0⟩ := (tick_send_of_honestSendAt M F R E) hlB hmB
    have hInv0 : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C s)) := by
      rw [show x.tickInput p (M.slotStart S.C s) = x.st iB p by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlB]]
      exact (lem11_node_invariant M F S A x R E iB p (E.not_mem_corrupted_of_tick hlB)).1
    -- Lemma 19 over the record: a proposal is for a slot greater than `0`
    have hpos := ((GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n0 _
      sent0 B hrun0 hInv0 hmem0).1
    have hΔ := one_le_Δ S
    have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s,
        Nat.mul_add, Nat.mul_one]
    have hsl : S.C.slot ((M.slotStart S.C s : ℕ) : Int) = s := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
        (by omega)
    rw [hsl] at hpos
    exact Nat.pos_iff_ne_zero.mp hpos
  have hg : B₁ ≠ Block.genesis := by
    rintro rfl
    exact hs0 hslot.symm
  -- `w`'s own relay of `B₁`, and the proposer of `B₁`
  obtain ⟨i, hi, hsendw, -, -⟩ := (tree_block_relayed M F) x R E (k := x.stepBefore t) hB₁ hg
  have hprop := ((F.nd.nodeInvCore_treeClosed ((lem11_node_invariantCore_of_run M F) S x R (x.stepBefore t) w).1).2 B₁ hB₁ hg).2.2.1
  rw [hslot, hps] at hprop
  have hauth : author (NamedObject.block B₁) = some p := hprop
  have hti : x.time (i + 1) ≤ t :=
    le_trans ((time_mono M) x R (by omega : i + 1 ≤ x.stepBefore t)) ((time_stepBefore_le M) x R E t)
  have hH : x.HonestThrough A (i + 1) p := (honestThrough_of_time_le M F) x R hp hti
  have hm := (sent_unforgeable M F) R E (i + 1) _ (NamedObject.block B₁) p
    ((mem_sent_of_mem_sub M F) x hsendw) (Or.inl rfl) hauth hH
  -- `p`'s own tick sent `B₁`, at the start of slot `s`
  obtain ⟨k', -, t'', hl', hdiff⟩ := (authored_from_own_tick M F) x R E hauth hm hH
  obtain ⟨-, n1, sent1, hrun1, hmem1⟩ := (tick_send_of_honestSendAt M F R E) hl' hdiff
  -- the tick's input state satisfies the node invariant (a wake keeps it)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput p t'') := by
    rw [show x.tickInput p t'' = x.st k' p by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl']]
    exact (lem11_node_invariant M F S A x R E k' p (E.not_mem_corrupted_of_tick hl')).1
  -- Lemma 19 over the record (T7, the field `tick_proposal` of `F.tk3`)
  obtain ⟨-, ht'', -, -, H, votes, sv, -, -, -, hB1eq⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n1 _ sent1 B₁
      hrun1 hInvT hmem1
  have hsl : S.C.slot (t'' : Int) = s := by
    rw [← hslot, hB1eq]
    rfl
  have htt : t'' = M.slotStart S.C s := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s
    rw [hsl] at ht''
    exact_mod_cast ht''.trans h.symm
  subst htt
  have hk : k' = iB := E.tick_unique k' iB p _ hl' hlB
  subst hk
  obtain ⟨-, n2, sent2, hrun2, hmem2, -, hall⟩ := (tick_send_step_outcome M F R E) hlB hmB
  exact F.tk.tick_block_unique S.C S.P S.X _ _ n2 sent2 B₁ B hrun2 (hall _ hdiff) hmem2

/-- The only slot-`s` block a validator holds at a step `k` is the honest proposer's, when the proposer is outside
the adversary set at `k`.

Why: `only_block_of_unforgeability`'s argument at the step `k`: the held block came with a relay by the holder at a
step before `k`, its author is the proposer, honest there (corruption is permanent), whose own tick to the start of
slot `s` sent it, and that tick sends one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `s`: the slot; `k`: the step; `B`: the proposal; `B₁`:
  the held block; `p`: the proposer; `w`: the holder.

Read aloud: the only slot-`s` block a validator holds at a step is the honest proposer's. -/
theorem only_block_of_unforgeability_st (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s k : ℕ) (B B₁ : Block V)
    (p w : V)
    (hp : p ∉ A.corrupted k) (hps : S.P.proposer s = p)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₁ : B₁ ∈ (x.st k w).tree) (hslot : B₁.slot = s) :
    B₁ = B := by
  obtain ⟨iB, hlB, hmB⟩ := hPropose
  -- the slot is positive: a tick runs at a time at least `1`
  have hs0 : s ≠ 0 := by
    obtain ⟨-, n0, sent0, hrun0, hmem0⟩ := (tick_send_of_honestSendAt M F R E) hlB hmB
    have hInv0 : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C s)) := by
      rw [show x.tickInput p (M.slotStart S.C s) = x.st iB p by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlB]]
      exact (lem11_node_invariant M F S A x R E iB p (E.not_mem_corrupted_of_tick hlB)).1
    -- Lemma 19 over the record: a proposal is for a slot greater than `0`
    have hpos := ((GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n0 _
      sent0 B hrun0 hInv0 hmem0).1
    have hΔ := one_le_Δ S
    have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s,
        Nat.mul_add, Nat.mul_one]
    have hsl : S.C.slot ((M.slotStart S.C s : ℕ) : Int) = s := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
        (by omega)
    rw [hsl] at hpos
    exact Nat.pos_iff_ne_zero.mp hpos
  have hg : B₁ ≠ Block.genesis := by
    rintro rfl
    exact hs0 hslot.symm
  -- `w`'s own relay of `B₁`, and the proposer of `B₁`
  obtain ⟨i, hi, hsendw, -, -⟩ := (tree_block_relayed M F) x R E (k := k) hB₁ hg
  have hprop := ((F.nd.nodeInvCore_treeClosed ((lem11_node_invariantCore_of_run M F) S x R k w).1).2 B₁ hB₁ hg).2.2.1
  rw [hslot, hps] at hprop
  have hauth : author (NamedObject.block B₁) = some p := hprop
  have hH : x.HonestThrough A (i + 1) p := fun i' hi' =>
    E.not_mem_corrupted_of_le (le_trans hi' (by omega : i + 1 ≤ k)) hp
  have hm := (sent_unforgeable M F) R E (i + 1) _ (NamedObject.block B₁) p
    ((mem_sent_of_mem_sub M F) x hsendw) (Or.inl rfl) hauth hH
  -- `p`'s own tick sent `B₁`, at the start of slot `s`
  obtain ⟨k', -, t'', hl', hdiff⟩ := (authored_from_own_tick M F) x R E hauth hm hH
  obtain ⟨-, n1, sent1, hrun1, hmem1⟩ := (tick_send_of_honestSendAt M F R E) hl' hdiff
  -- the tick's input state satisfies the node invariant (a wake keeps it)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput p t'') := by
    rw [show x.tickInput p t'' = x.st k' p by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl']]
    exact (lem11_node_invariant M F S A x R E k' p (E.not_mem_corrupted_of_tick hl')).1
  -- Lemma 19 over the record (T7, the field `tick_proposal` of `F.tk3`)
  obtain ⟨-, ht'', -, -, H, votes, sv, -, -, -, hB1eq⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n1 _ sent1 B₁
      hrun1 hInvT hmem1
  have hsl : S.C.slot (t'' : Int) = s := by
    rw [← hslot, hB1eq]
    rfl
  have htt : t'' = M.slotStart S.C s := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s
    rw [hsl] at ht''
    exact_mod_cast ht''.trans h.symm
  subst htt
  have hk : k' = iB := E.tick_unique k' iB p _ hl' hlB
  subst hk
  obtain ⟨-, n2, sent2, hrun2, hmem2, -, hall⟩ := (tick_send_step_outcome M F R E) hlB hmB
  exact F.tk.tick_block_unique S.C S.P S.X _ _ n2 sent2 B₁ B hrun2 (hall _ hdiff) hmem2

/-! ## The witnessed caches -/

section Witnessed

section Execution

open Framework.StsMultisetLog (AtomicStep Event TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react applyNodeStepResult_getElem receive_getElem NodeStepResult View)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)

/-- Every step of the wiring on one event, from a node state satisfying the model's node
invariant (a tick at a reading no earlier than the node's clock), keeps the node's tree and
carries `CachesWitnessed M S.C` from the node state to the step's state: a tick step is an answer of
the node's tick or keeps the state, a delivery runs the dispatch, a wake writes `awakeSince` only.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result.

Read aloud: every step of the node from a node state satisfying the invariant, a tick at a reading
no earlier than the node's clock, keeps the tree and keeps the node's justification and its greatest
chain-state height witnessed by blocks of its tree. -/
theorem reaction_witnessedFrom (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n e res)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv S.C S.P S.X n)
    -- the node's clock is at most the reading
    (hr : n.t ≤ (r : Int)) :
    n.tree ⊆ res.state.tree ∧ (CachesWitnessed M S.C n → CachesWitnessed M S.C res.state) := by
  cases e with
  | tick =>
      rcases ((GoldilocksCorrectness.Record.step_tick_iff M) S p r view n res).1 hstep with
        ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact F.tkAdded.tick_witnessedFrom S.C S.P S.X n (r : Int) n' sent hok hI hr
      · exact ⟨Finset.Subset.refl _, id⟩
  | recv m =>
      rw [((GoldilocksCorrectness.Record.step_recv_iff M) S p r view n m res).1 hstep]
      exact F.rcvAdded.receive_witnessedFrom S.C S.P S.X n m.msg hI
  | wake =>
      rw [((GoldilocksCorrectness.Record.step_wake_iff M) S p r view n res).1 hstep]
      -- a wake keeps the tree, the finalized and the justified blocks and the justification height
      obtain ⟨-, -, hT, hFin, hJ, hJh, -⟩ := F.wk.wake_readers n (r : Int)
      refine ⟨by show M.tree n ⊆ M.tree (M.wake n (r : Int)); rw [hT], fun hc => ?_⟩
      show CachesWitnessed M S.C (M.wake n (r : Int))
      unfold CachesWitnessed GoldilocksCorrectness.Record.Statements.Routines.hMax at hc ⊢
      simp only [GoldilocksModel.N.tree, GoldilocksModel.N.finalized, GoldilocksModel.N.justified,
        GoldilocksModel.N.justifiedHeight] at hc ⊢
      rw [hT, hFin, hJ, hJh]
      exact hc
  | custom ev => exact ev.elim

/-- At every step of every execution, every validator's node state satisfies
`CachesWitnessed M S.C`. By induction on the step: the initial node state does (the genesis block
witnesses all three clauses), and every step relates the node state before to the node state after,
the chain states of the tree before being the blocks' own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step, every validator's justification and greatest chain-state height are
witnessed by blocks of its tree. -/
theorem cachesWitnessed_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    CachesWitnessed M S.C (x.st i v) := by
  induction i with
  | zero =>
      rw [R.init v]
      -- the initial tree is the genesis block alone, which witnesses all three clauses
      have hg := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_J M F) S.C
      have hH : GoldilocksCorrectness.Record.Statements.Routines.hMax M S.C (M.initial S.C v) =
          (M.chainStateOf S.C Block.genesis).h := by
        unfold GoldilocksCorrectness.Record.Statements.Routines.hMax
        rw [F.init.initial_tree S.C v, Finset.sup_singleton]
      unfold CachesWitnessed
      rw [hH, F.init.initial_tree S.C v, F.init.initial_justified S.C v,
        F.init.initial_justifiedHeight S.C v, F.init.initial_finalized S.C v]
      exact ⟨⟨Block.genesis, Finset.mem_singleton_self _, hg.1.symm, hg.2.symm⟩,
        ⟨Block.genesis, Finset.mem_singleton_self _, rfl⟩,
        ⟨Block.genesis, Finset.mem_singleton_self _, ancestorEq_refl _, Nat.sub_le _ _⟩⟩
  | succ i ih =>
      rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hl, hact, hrun, h, -⟩ | ⟨sm, -, hact, h⟩ |
          ⟨⟨tR, keep, hlR⟩, -, hwake⟩
      · rw [h]
        exact ih
      · -- a tick, by an active validator, from the state at its step, at a clock value no earlier than
        -- the node's clock
        have hv : v ∉ A.corrupted i := Activity.not_mem_corrupted_of_mem_active hact
        obtain ⟨hI, -, ht⟩ := lem11_node_invariant M F S A x R E i v hv
        have hin : x.tickInput v t = x.st i v := by
          unfold Trace.tickInput
          rw [(tickStep_eq_of_lbl M) x E hl]
        rw [hin] at hrun
        have htt : (x.st i v).t ≤ (t : Int) := by
          rw [ht]
          exact_mod_cast E.clockValue_le_of_set hv (Or.inl hl)
        rw [h]
        exact (F.tkAdded.tick_witnessedFrom S.C S.P S.X _ (t : Int) n' sent hrun hI htt).2 ih
      · -- a delivery, to an active validator
        have hv : v ∉ A.corrupted i := Activity.not_mem_corrupted_of_mem_active hact
        obtain ⟨hI, -, -⟩ := lem11_node_invariant M F S A x R E i v hv
        rw [h]
        exact (F.rcvAdded.receive_witnessedFrom S.C S.P S.X _ sm.msg hI).2 ih
      · -- a wake keeps the tree, the finalized and the justified blocks and the justification height
        rw [hwake tR keep hlR]
        obtain ⟨-, -, hT, hFin, hJ, hJh, -⟩ := F.wk.wake_readers (x.st i v) (tR : Int)
        unfold CachesWitnessed GoldilocksCorrectness.Record.Statements.Routines.hMax at ih ⊢
        simp only [GoldilocksModel.N.tree, GoldilocksModel.N.finalized, GoldilocksModel.N.justified,
          GoldilocksModel.N.justifiedHeight] at ih ⊢
        rw [hT, hFin, hJ, hJh]
        exact ih

/-- `cachesWitnessed_of_exec` before the time `t`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: before every time, every validator's justification and greatest chain-state height are
witnessed by blocks of its tree. -/
theorem cachesWitnessed_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    CachesWitnessed M S.C (x.stateBefore t v) :=
  (cachesWitnessed_of_exec M F) S A x R E (x.stepBefore t) v

end Execution

end Witnessed

/-! ## Every frame has a viable head -/

/-- **Every frame of a node state of the execution has a viable head, at a step.** For every step `i`
and every validator `v`, one in the adversary set included, the frame of `x.st i v` has a viable
head: the clock-free part of the node invariant (`lem11_node_invariantCore_of_run`), the finalized
block an ancestor of the justified one, the justification cache, and the caches witnessed.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `i`: the step; `v`: the validator.

Read aloud: every frame of a node state at a step has a viable head. -/
theorem frame_has_viable_head_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    ∃ W : Block V, W ∈ (M.fg_to_ac (x.st i v)).viable_heads := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R i v).1
  exact (GoldilocksCorrectness.Record.Proofs.Routines.exists_viable_head_of_witnessed_of_core M F) S.C S.P S.X _ hInv
    ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E i v)
    ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i v).2.2.1
    ((cachesWitnessed_of_exec M F) S A x R E i v)

/-- Every frame of a node state has a viable head. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the
  validator.

Read aloud: every frame of a node state has a viable head. -/
theorem frame_has_viable_head (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    ∃ W : Block V, W ∈ (M.fg_to_ac (x.stateBefore t v)).viable_heads := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) v).1
  exact (GoldilocksCorrectness.Record.Proofs.Routines.exists_viable_head_of_witnessed_of_core M F) S.C S.P S.X _ hInv
    ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_stateBefore M F) S A x R E t v)
    ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.stepBefore t) v).2.2.1
    ((cachesWitnessed_of_stateBefore M F) S A x R E t v)

/-! ## The locks in box 2 -/

/-- A record lock is the root of the justified block of the chain state of a block the validator
held at an earlier step, justified at the lock's height, which is at least `1`: the lock was
written by an attestation of the validator's tick, whose finality pair is its head's justification.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `v`: the validator;
  `h`: the height; `T'`: the lock.

Read aloud: a lock of a validator's record is on the justified block of the chain state of a block
it held at an earlier step, justified at the lock's height, which is at least `1`. -/
theorem lock_justified_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (k : ℕ) (v : V) (h : Height) (T' : BlockId)
    (hLock : (x.st k v).sentLock h = some T') :
    ∃ j < k, ∃ D ∈ (x.st j v).tree, 1 ≤ h ∧ (M.chainStateOf S.C D).h_j = h ∧
      (M.chainStateOf S.C D).J.root = T' := by
  obtain ⟨c, hc, hcfp⟩ := (((GoldilocksCorrectness.Record.Statements.Executions.recordConsistent_of_exec M F) S A x R E k v).lockRec h T').1 hLock
  obtain ⟨j, t', a, hj, hl, -, hsent, -, hac, -⟩ := (record_content_sent_step M F) S A x R E v k c hc
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  -- the tick's input state satisfies the node invariant (a wake keeps it)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t') := by
    rw [show x.tickInput v t' = x.st j v by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E (i := j) (v := v) (by assumption)]]
    exact (lem11_node_invariant M F S A x R E j v (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 49 over the record (T8, the field `tick_attestation` of `F.tk3`): the validator client
  -- built `a` from the chain state of the head, the end of the walk from the anchor over the input
  -- state's frame (`AttestationFrom`)
  obtain ⟨-, -, source, head, -, ⟨_, _, -, hW⟩, ⟨τ, -, -, hadef⟩, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  -- the head is a block of the input state's tree, which is `v`'s tree at step `j`
  have hhead := (GoldilocksCorrectness.Record.Proofs.Routines.ac_to_fg_head_mem M F) S.C S.P S.X _ hInvT
    _ _ _ _ head hW.1
  have hHT : head ∈ (x.st j v).tree := by
    rw [show x.st j v = x.tickInput v t' by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]]
    exact hhead.1
  -- the record's lock is the finality pair of `a`, which is the head's justification
  have hfp : a.finality_pair = some ⟨h, T'⟩ := by
    rw [← hcfp, ← hac]
    rfl
  rw [hadef] at hfp
  dsimp only at hfp
  split at hfp
  · rename_i q hq
    split at hfp
    · cases hfp
    · cases hfp
      obtain ⟨hpair, hFj, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.finality_pair_some M F) hq
      injection hpair with hh hT
      refine ⟨j, hj, head, hHT, ?_, hh.symm, hT.symm⟩
      rw [hh]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hFj
  · cases hfp

/-- When `p` is in box 2 with the justified block `J₀`, every lock at `p`'s greatest chain-state
height minus one is on `J₀`. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `t`: the time;
  `v`: the validator whose record is read; `p`: the validator in box 2; `J₀`: its justified block;
  `T'`: the lock.

Read aloud: in box 2 at the justified height, every lock is on the justified block. -/
theorem lockBox_of_one_justification (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v p : V)
    (J₀ : Block V) (T' : BlockId)
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) t)
    (hBox : BoxTwo M S.C (x.stateBefore t p) J₀)
    (hLock : (x.stateBefore t v).sentLock (hMax M S.C (x.stateBefore t p) - 1) = some T') :
    T' = J₀.root := by
  obtain ⟨hbox, -, hJ⟩ := hBox
  rw [hbox, Nat.add_sub_cancel] at hLock
  obtain ⟨j, hj, D', hD'T, h1, hD'j, hD'J⟩ := (lock_justified_of_exec M F) S A x R E _ v _ T' hLock
  obtain ⟨⟨D, hDT, hDJ, hDj⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t p
  have hcert' := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D').1 (hD'j ▸ h1)).1
  have hcert := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 (hDj ▸ h1)).1
  rw [hD'j] at hcert'
  rw [← hDj] at hcert
  have hAdv' : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time j) (x.time (x.stepBefore t))) := by
    have hk := (time_stepBefore_le M) x R E t
    have hjk := (time_mono M) x R (Nat.le_of_lt hj)
    exact hAdv.mono (max_le (by linarith) hk)
  have hroot := (lem76_honest_one_justification M F Fx) S A x R E j (x.stepBefore t) v p hAdv' D' D
    hD'T hDT _ _ _ hcert' hcert
  rw [← hD'J, hroot, ← hDJ, hJ]

/-- Every validator's tick step to the clock value `c` is at a real time at most `c + ΔClockBehind`: when `v` ticks to
`c`, by `tick_active`; when it does not, `x.tickStep v c` is step `0`, at the real time `0`.

The variables:
- `M`: the model; `F`: its facts; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
  `v`: the validator; `c`: the clock value.

Read aloud: the step of `v`'s tick to `c` is at a real time at most `c` plus the behind bound. -/
theorem time_tickStep_le_add_behind {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (v : V) (c : ℕ) :
    x.time (x.tickStep v c) ≤ (c : ℝ) + ΔClockBehind := by
  by_cases hk : ∃ i : ℕ, x.lbl i = Event.tick v c
  · exact (E.time_tickStep hk).2
  · have h0 : x.tickStep v c = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hk]
    rw [h0, R.time_zero]
    have := E.behind_nonneg
    positivity

/-- The adversary bound up to a real time at least `c + ΔClockBehind` is the bound up to the real time of every
validator's tick step to `c`.

The variables:
- `M`: the model; `F`: its facts; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
  `v`: the validator; `c`: the clock value; `t`: the real time of the bound.

Read aloud: fewer than a third corrupted up to `t` gives fewer than a third corrupted up to `v`'s tick to `c`, when
`c` plus the behind bound is at most `t`. -/
theorem adversaryFewerThanThirdUntil_tickStep {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (v : V) (c : ℕ) {t : ℝ} (ht : (c : ℝ) + ΔClockBehind ≤ t)
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) t) :
    A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time (x.tickStep v c)) :=
  hAdv.mono (le_trans ((time_tickStep_le_add_behind M F) x R E v c) ht)

/-- `lockBox_of_one_justification` at the tick inputs: when `p` is in box 2 with the justified block `J₀` at its tick
to `c`, every lock of `v`'s tick input to `c` at `p`'s greatest chain-state height minus one is on `J₀`, given the
adversary bound up to the later real time of the two ticks.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the environment's facts; `c`: the
  clock value; `v`: the validator whose lock is read; `p`: the validator in box 2; `J₀`: its justified block; `T'`: the
  lock.

Read aloud: in box 2 at the justified height, every lock read at a tick to `c` is on the justified block. -/
theorem lockBox_of_one_justification_tick (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (c : ℕ) (v p : V)
    (J₀ : Block V) (T' : BlockId)
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (x.tickStep v c)) (x.time (x.tickStep p c))))
    (hBox : BoxTwo M S.C (x.tickInput p c) J₀)
    (hLock : (x.tickInput v c).sentLock (hMax M S.C (x.tickInput p c) - 1) = some T') :
    T' = J₀.root := by
  obtain ⟨hbox, -, hJ⟩ := hBox
  rw [hbox, Nat.add_sub_cancel] at hLock
  obtain ⟨j, hj, D', hD'T, h1, hD'j, hD'J⟩ := (lock_justified_of_exec M F) S A x R E (x.tickStep v c) v _ T' hLock
  obtain ⟨⟨D, hDT, hDJ, hDj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (x.tickStep p c) p
  have hcert' := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D').1 (hD'j ▸ h1)).1
  have hcert := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 (hDj ▸ h1)).1
  rw [hD'j] at hcert'
  rw [← hDj] at hcert
  have hAdv' : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time j) (x.time (x.tickStep p c))) := by
    have hjk := (time_mono M) x R (Nat.le_of_lt hj)
    exact hAdv.mono (max_le (le_trans hjk (le_max_left _ _)) (le_max_right _ _))
  have hroot := (lem76_honest_one_justification M F Fx) S A x R E j (x.tickStep p c) v p hAdv' D' D
    hD'T hDT _ _ _ hcert' hcert
  rw [← hD'J, hroot, ← hDJ]
  exact congrArg Block.root hJ

/-! ## An honest vote extends its voter's root -/

/-- An honest Goldfish vote names a block its voter holds, on the chain of the voter's own
fork-choice root. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote.

Read aloud: an honest Goldfish vote names a block its voter holds, on the chain of the voter's own
fork-choice root. -/
theorem vote_extends_own_root (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s' : ℕ) (u : V) (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree, vote.head = H_u.root ∧
      (M.get_fc_root (x.tickInput u (M.voteTime S.C s'))).AncestorEq H_u := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  obtain ⟨i, hl, hm⟩ := hSend
  have hTI_hSB : x.tickInput u (M.voteTime S.C s') = x.st i u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  obtain ⟨-, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  -- the tick's input state satisfies the node invariant: the tick is by an active validator
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput u (M.voteTime S.C s')) := by
    rw [hTI_hSB]
    exact (lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 14 over the record (T5, the field `tick_vote_head` of `F.tk3`): the vote is for the end
  -- `H_u` of the walk through the viable part of `u`'s voter tree, from the anchor over `u`'s
  -- frame with the lock entries the tick left (`HeadOf`)
  obtain ⟨-, -, -, -, -, H_u, ⟨votes, support_votes, -, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInv hvote
  refine ⟨H_u, ?_, hhead, ?_⟩
  · -- the walk's end is a block `u` holds: a block of the viable part of the voter's tree, or the
    -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable
    -- tree
    have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))).tree,
        D ∈ (x.tickInput u (M.voteTime S.C s')).tree :=
      fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))) n'.lockEntries
          ((M.voteTime S.C s' : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInv]
        split
        · exact F.nd.nodeInv_justifiedInTree hInv
        · exact F.nd.nodeInv_finalized_mem_tree hInv
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _
        H_u).1 h1).1
  · -- the anchor is the fgroot or a descendant of it, and the walk's end is the anchor or a
    -- descendant of it
    have hRA : (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))).fc_root.AncestorEq
        (GoldilocksCorrectness.Record.Statements.Routines.AnchorAt M
          (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))) n'.lockEntries
          ((M.voteTime S.C s' : ℕ) : Int)) := by
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))) n'.lockEntries
          ((M.voteTime S.C s' : ℕ) : Int) with h | h
      · rw [h]
        exact ancestorEq_refl _
      · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)
      (x.tickInput u (M.voteTime S.C s'))]
    exact ancestorEq_trans hRA (GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1)

end GoldilocksCorrectness.Record.Proofs.Executions

