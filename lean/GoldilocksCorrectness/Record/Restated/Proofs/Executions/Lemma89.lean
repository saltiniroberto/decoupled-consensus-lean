module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89fStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma36a
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 89's kit, where an opening whose window an
object's arrivals break lies, the phase's members awake, the front from `FrontWindowStable`, the
proposer's frame, the negation of the quiet round and of `FrontWindowStable` written out, and the
classification of the justified block, the finalized block and a `head_height_floor` past a height.
The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono supportCutoff_cast
  supportCutoff_eq supportCutoff_mono voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes tau_of_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (advQ_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (InSpan Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The span premise -/

/-! ## Where the spans go -/

omit [RootOrder] in
/-- **An opening whose window an object's arrivals break lies in the span of `k + 2` slots from
the slot of the first arrival.** With `σ` the slot of the object's first arrival at time `t`, and
an arrival at some member at a time `t'` from `t` to `t + Δ`: when `t'` is at or after the vote time
of slot `s − k − 1` and before the vote time of slot `s` (`k + 1 ≤ s`), the slot `s` is in
`[σ, σ + k + 2)`. The window reads `k + 1` slots, and the arrivals' spread over one delay adds one.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the honest round opening slot; `σ`: the slot of the first arrival;
- `t`, `t'`: the first arrival and the member's arrival.

Read aloud: a slot whose window an object's arrivals break is at most `k + 1` slots after the slot
of the object's first arrival. -/
theorem broken_window_in_window_span (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s σ t t' : ℕ) (hk : S.C.k + 1 ≤ s)
    (hσ : M.slotStart S.C σ ≤ t) (hσ' : t < M.slotStart S.C (σ + 1))
    (ht : t ≤ t') (ht' : t' ≤ t + Δ S)
    (hw₁ : M.voteTime S.C (s - S.C.k - 1) ≤ t') (hw₂ : t' < M.voteTime S.C s) :
    InSpan σ (S.C.k + 2) s := by
  have hΔ := one_le_Δ S
  have e₂ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s - S.C.k - 1)
  have e₃ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at e₂ e₃ hσ hσ'
  have h₁ : 4 * Δ S * (s - S.C.k - 1) < 4 * Δ S * (σ + 1) := by omega
  have h₁' := Nat.lt_of_mul_lt_mul_left h₁
  have h₅ : 4 * Δ S * σ < 4 * Δ S * (s + 1) := by
    rw [Nat.mul_add_one (4 * Δ S) s]
    omega
  have h₂ := Nat.lt_of_mul_lt_mul_left h₅
  unfold InSpan
  exact ⟨by omega, by omega⟩

/-! ## The committee premise's anchor -/

/-! ## The hypotheses of the round lemmas from the phase's member sets -/

/-- **The re-base's members are awake and honest through the update of slot `s`.** Under
permanent corruption, with every validator honest at a time of the phase awake then, the duty
window of slot `s` starting at or after `tGAT` and the support cutoff of slot `s + 1` inside the
phase: every member of `roundMembers M S Sched (s + 1)` is awake and honest at every time from the
duty window's start of slot `s` to the support cutoff of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`: the setup, the schedule; `tGAT`, `tAwakeEnd`: the ends of the phase; `s`: the
  slot.

Read aloud: the members of the round of slot `s + 1` are awake and honest from the duty window of
slot `s` to the support cutoff of slot `s + 1`. -/
theorem rebase_window_of_roundMembers (S : Setup V) (A : Activity V) (tGAT tAwakeEnd s : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hsw : tGAT ≤ M.dutyWindowStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    ∀ v ∈ roundMembers M S A x (s + 1),
      v ∈ A.activeThroughout x (M.dutyWindowStart S.C s) (M.supportCutoff S.C (s + 1)) := by
  intro v hv
  simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
  exact (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake hsw hEnd hv

/-- **The base at an opening's slot `s`, from a stable window.** `lem89fq_front` with
`s_w := s − 2k` and `s' := s − 1`: when the frames of the members are stable through the `2k − 1`
slots before `s`, the chain invariant and the lock invariant hold at slot `s − 1` for the family
of the members' live lock blocks and roots.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times of the phase; `s`: the honest round opening slot; `Hon`: one member set per slot.

Roots name blocks until `M.supportCutoff S.C (s - 1)`: `lem89fq_front` at `s' := s − 1`.

Read aloud: a window stable through the `2k − 1` slots before `s` gives the chain invariant and the
lock invariant at slot `s − 1` for the family of the members' live lock blocks and roots. -/
theorem front_of_frontWindowStable (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (Hon : ℕ → Finset V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s - 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s − 1` (, for `lem89fq_front`)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST ≤ tGAT)
    (hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 2 * S.C.k))
    (hk : 2 * S.C.k ≤ s)
    (hHonMono : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ < s - 1 → Hon (s₁ + 1) ⊆ Hon s₁)
    (hHon : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ ≤ s - 1 → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : ∀ s₁, s - 2 * S.C.k + S.C.k ≤ s₁ → s₁ ≤ s - 1 →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    (hsw : tGAT ≤ M.dutyWindowStart S.C (s - 2 * S.C.k))
    (hEnd : M.supportCutoff S.C (s - 1 + 1) ≤ tAwakeEnd)
    (hStable : FrontWindowStable M S A x Hon (s - 2 * S.C.k) (s - 1)) :
    ChainInvFor M S A x (Hon (s - 1)) (FrontFamily M S A x (Hon (s - 1)) (s - 1)) (s - 1) ∧
    ∀ u ∈ Hon (s - 1),
      LiveLocksOnFamilyAt M S A x (FrontFamily M S A x (Hon (s - 1)) (s - 1)) (s - 1) u :=
  (GoldilocksCorrectness.Record.Statements.Executions.lem89fq_front M F U) S A x R GST tGAT tAwakeEnd
    (s - 2 * S.C.k) (s - 1) Hon E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST hGSTw
    hHonMono hHon hAwake hActive hCommittees hsw (by omega) hEnd hStable.1 hStable.2

/-- **The proposer clause relative to `C` gives a viable head on `C`'s chain.** When, before `t`,
`p`'s fork-choice root is compatible with `C` and, if it is `C` or an ancestor of `C`, some viable
head of `p`'s frame is `C` or a descendant of `C`, then some viable head of `p`'s frame is `C` or a
descendant of `C`.

Why: when the root is not `C` or an ancestor of `C`, compatibility makes `C` an ancestor of the
root, and every viable head descends from the root.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator;
  `C`: the block.

Read aloud: the proposer clause relative to `C` gives a viable head of `p`'s frame that is `C` or a
descendant of `C`. -/
theorem frameP_of_proposerClause (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (p : V) (C : Block V)
    (hClause : (M.fg_to_ac (x.stateBefore t p)).fc_root.compatible C = true ∧
      ((M.fg_to_ac (x.stateBefore t p)).fc_root.AncestorEq C →
        ∃ W ∈ (M.fg_to_ac (x.stateBefore t p)).tree,
          W ∈ (M.fg_to_ac (x.stateBefore t p)).viable_heads ∧ C.AncestorEq W)) :
    ∃ W ∈ (M.fg_to_ac (x.stateBefore t p)).tree,
      W ∈ (M.fg_to_ac (x.stateBefore t p)).viable_heads ∧ C.AncestorEq W := by
  by_cases hroot : (M.fg_to_ac (x.stateBefore t p)).fc_root.AncestorEq C
  · exact hClause.2 hroot
  · have hCρ : C.AncestorEq (M.fg_to_ac (x.stateBefore t p)).fc_root :=
      ((compatible_iff _ _).1 hClause.1).resolve_left hroot
    obtain ⟨W, hW⟩ := (GoldilocksCorrectness.Record.Statements.Executions.frame_has_viable_head M F) S A x R E
      t p
    have hW' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
      (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) p).1 W).1 hW
    exact ⟨W, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW'.1, hW'.2.1⟩, hW,
      ancestorEq_trans hCρ hW'.2.2.1⟩

/-- **A viable head on the chain of an ancestor of the proposal's parent.** When `B.parent` is in
the viable tree of `p`'s frame before `t` and `C` is `B.parent` or an ancestor of it, some viable
head of `p`'s frame is `C` or a descendant of `C`.

Why: a block of the viable tree has a viable head among its descendants.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator;
  `B`: the proposal; `C`: the block.

Read aloud: when the proposal's parent is in the viable tree of `p`'s frame, every ancestor of it
has a viable head among its descendants. -/
theorem frameP_of_viableTree_parent (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t : ℕ) (p : V) (B C : Block V)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.stateBefore t p))
      (M.fg_to_ac (x.stateBefore t p)).tree)
    (hC : C.AncestorEq B.parent) :
    ∃ W ∈ (M.fg_to_ac (x.stateBefore t p)).tree,
      W ∈ (M.fg_to_ac (x.stateBefore t p)).viable_heads ∧ C.AncestorEq W := by
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F), Finset.mem_inter] at hParentIn
  obtain ⟨_, _, W, ⟨hWtree, hWvh⟩, hBW⟩ := hParentIn
  exact ⟨W, hWtree, hWvh, ancestorEq_trans hC hBW⟩

/-- **A failed proposer clause at a holder of the block is an event.** When the proposer clause
relative to `B` fails at `w` before `t` and `w` holds `B` then, `w`'s root before `t` is not `B` or
an ancestor of `B`, or its `head_height_floor` is greater than `B`'s chain-state height.

Why: when the root is `B` or an ancestor of `B`, `B` is in the frame tree (the finalized block is
an ancestor of the root), and with the `head_height_floor` at most `B`'s height `B` would itself
be a viable head.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the validator;
  `B`: the block.

Read aloud: a holder of `B` whose proposer clause relative to `B` fails has its root off `B`'s chain
or its `head_height_floor` greater than `B`'s chain-state height. -/
theorem proposerClause_fail_event (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (w : V) (B : Block V)
    (hBw : B ∈ (x.stateBefore t w).tree)
    (hFail : ¬ ((M.fg_to_ac (x.stateBefore t w)).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.stateBefore t w)).tree,
          W ∈ (M.fg_to_ac (x.stateBefore t w)).viable_heads ∧ B.AncestorEq W))) :
    RootOffChainAt M S A x w t B ∨
      HeadHeightFloorPastAt M S A x w t (M.chainStateOf S.C B).h := by
  by_cases hroot : (M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq B
  · right
    have hF : (x.stateBefore t w).finalized.AncestorEq B :=
      ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E t w)
        (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hroot)
    unfold HeadHeightFloorPastAt
    by_contra hle
    push Not at hle
    apply hFail
    refine ⟨(compatible_iff _ _).2 (Or.inl hroot),
      fun _ => ⟨B, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBw, hF⟩, ?_, ancestorEq_refl B⟩⟩
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
      (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) w).1 B).2 ⟨hBw, hF, hroot, hle⟩
  · left
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hroot
    exact hroot

/-- A bound on the attestations sent before `t` by the validators honest at `t` holds before every
earlier time, for the same senders.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t'`, `t`: the two times; `H`: the
  bound.

Read aloud: a bound on the heights of the attestations sent before `t` by the validators honest at
`t` holds before every earlier time. -/
theorem oldAttestationsAtMost_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t' t H : ℕ) (htt : t' ≤ t)
    (h : OldAttestationsAtMostHonestAt M S A x t t H) : OldAttestationsAtMostHonestAt M S A x t' t H :=
  fun i t₁ v a hl ht₁ hHon hsent => h i t₁ v a hl (lt_of_lt_of_le ht₁ (by exact_mod_cast htt)) hHon hsent

/-! ## A round that is not quiet -/

/-- **A round that is not quiet relative to its own confirmations, written out.** When
`QuietRoundOnConfirmations M S Sched x Hon B s s''` fails: some member of `Hon s` has its root off
`B.parent`'s chain or its `head_height_floor` past `h(B.parent)` in the state its tick to the vote
time of slot `s` starts from, or its root off `B`'s chain or its `head_height_floor` past `h(B)` in
the state its tick to the action time starts from; or at a slot `s'` of the round some member of
`Hon (s' + 1)` fails `StepFrameAt` relative to `B`; or relative to a confirmation a member of
`Hon σ` saved for a slot `σ` from `s − 1` to `s'`; or the proposer of slot `s''` has, in the state
its tick to the start of slot `s''` starts from, its root off the chain of every confirmation of
slot `s'' − 2` a member of `Hon (s'' − 2)` saved, or no viable head on that confirmation's chain.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: one member set per slot;
- `B`: the round's proposal; `s`: its first slot; `s''`: the next honest round opening slot.

Read aloud: a round that is not quiet relative to its own confirmations has a member whose root or
`head_height_floor` breaks the round, a member failing `StepFrameAt` relative to the proposal or to
a saved confirmation, or a next proposer whose frame misses every saved confirmation of slot
`s'' − 2`. -/
theorem quietRound_cases (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    (hNotQuiet : ¬ QuietRoundOnConfirmations M S A x Hon B s s'') :
    (∃ w ∈ Hon s,
      RootOffChainAtTick M S A x w (M.voteTime S.C s) B.parent ∨
      HeadHeightFloorPastAtTick M S A x w (M.voteTime S.C s) (M.chainStateOf S.C B.parent).h ∨
      RootOffChainAtTick M S A x w (M.supportCutoff S.C (s + 1)) B ∨
      HeadHeightFloorPastAtTick M S A x w (M.supportCutoff S.C (s + 1))
        (M.chainStateOf S.C B).h) ∨
    (∃ s', s ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt M S A x B s' w) ∨
    (∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ σ, s - 1 ≤ σ ∧ σ ≤ s' ∧ ∃ v ∈ Hon σ,
      ∃ C : Block V,
        (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C ∧
        ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt M S A x C s' w) ∨
    (∀ C : Block V,
      (∃ v ∈ Hon (s'' - 2),
        (x.tickOutput v (M.supportCutoff S.C (s'' - 1))).savedConfirmation (s'' - 2) =
          some C) →
      ¬
        ((M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).fc_root.AncestorEq
            C ∧
        ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).viable_heads ∧
          C.AncestorEq W)) := by
  unfold QuietRoundOnConfirmations at hNotQuiet
  by_contra hNone
  apply hNotQuiet
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun s' hs hs' w hw => ?_,
    fun s' hs hs' σ hσ hσ' v hv C hC w hw => ?_, ?_⟩
  · by_contra hc
    apply hNone
    left
    refine ⟨w, hw, ?_⟩
    by_cases h1 : (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent
    · right; left
      unfold HeadHeightFloorPastAtTick
      by_contra h2
      exact hc ⟨h1, Nat.le_of_not_lt h2⟩
    · left; exact h1
  · by_contra hc
    apply hNone
    left
    refine ⟨v, hv, ?_⟩
    by_cases h1 : (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq B
    · right; right; right
      unfold HeadHeightFloorPastAtTick
      by_contra h2
      exact hc ⟨h1, Nat.le_of_not_lt h2⟩
    · right; right; left; exact h1
  · by_contra hc
    exact hNone (Or.inr (Or.inl ⟨s', hs, hs', w, hw, hc⟩))
  · by_contra hc
    exact hNone (Or.inr (Or.inr (Or.inl ⟨s', hs, hs', σ, hσ, hσ', v, hv, C, hC, w, hw, hc⟩)))
  · by_contra hc
    apply hNone
    refine Or.inr (Or.inr (Or.inr fun C hC hCl => hc ⟨C, hC, hCl⟩))

/-! ## The two classification facts -/

/-- **A held block certified at a height greater than `h₀ + 1` is an entry of the honest chain.**
Under unforgeability, roots naming blocks, permanent corruption and fewer than a quorum ever
corrupted up to `t`, with every honest attestation sent before the support cutoff of slot
`s₀ + 1` at a height at most `h₀ + 1`: when `w`, honest at `t`, holds before `t` a block `D` whose
chain carries a justification certificate at a height `h > h₀ + 1` for `T`, an ancestor of `D` or
`D` itself, then `T` is an entry block on the honest chain from `s₀` at a slot `s_a` whose update
ran by `t`.

Why: `cert_entry_at_slot` names an entry `E` with `T`'s root at such a slot, and the roots naming
blocks make it `T`, which `w` holds.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the holder; `D`: the held
  block; `T`: the certified block; `h`: the certificate's height.

Roots name blocks until `t`: the proof compares `T`, held by `w` at the step before `t`, with
the entry of the honest chain at a slot whose update ran by then.

Read aloud: a block certified at a height greater than `h₀ + 1` on the chain of a block an honest
validator holds is an entry of the honest chain at a slot whose update ran by `t`. -/
theorem justified_entry_of_cert (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t h₀ : ℕ) (w : V) (D T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ A.corruptedAtTime x t)
    -- `w` holds `D` before `t`, and `T` is `D` or an ancestor of `D`
    (hD : D ∈ (x.stateBefore t w).tree) (hTD : T.AncestorEq D)
    -- `D`'s chain carries a justification certificate at `h` for `T`
    (hc : JustificationCertOn M D h T)
    (hh : h₀ + 1 < h) :
    ∃ s_a : ℕ, (∃ (k : ℕ) (u : V), x.time k ≤ t ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧ OnHonestChainAt M S A x s₀ s_a T ∧
      IsEntry M S.C T := by
  set j := x.stepBefore t with hjdef
  have hjt : x.time j ≤ t := (time_stepBefore_le M) x R E t
  have hwj : w ∉ A.corrupted j := (not_mem_corrupted_of_le_time M) x R E hw (by exact_mod_cast hjt)
  have hAdvQj : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time j) (M.supportCutoff S.C (s₀ + 1))) :=
    (fun X hX => hAdvQ X (fun v hv => let ⟨t'', h1, h2⟩ := hX v hv;
      ⟨t'', le_trans h1 (max_le_max hjt le_rfl), h2⟩))
  have hD' : D ∈ (x.st j w).tree := hD
  obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, hEb, hEon, hEent, -, hroot⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ (h₀ + 1) j w
    D T h E hAdvQj hOld hD' ((progressCertOn_of_justificationCertOn M F) hc) hh
  have hTT : T ∈ (x.st j w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w D T hD' hTD
  have hkt : x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) ≤ t :=
    le_trans ((time_mono M) x R hk.le) hjt
  -- the attester held the entry at its tick, a step before `j`: one root, so one block
  have hEq : T = Eb := hRoots _ _
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjt hTT)
    ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl hkt hEb) hroot
  subst hEq
  exact ⟨s_a, ⟨_, uₐ, hkt, hl⟩, hEon, hEent⟩

/-- **The justified block is old, or an entry of the honest chain confirmed by `t`.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a quorum ever corrupted
up to `t`, with every honest attestation sent before the support cutoff of slot `s₀ + 1` at a
height at most `h₀ + 1`: when `w` is honest at `t`, its justified block `J` before `t` has
chain-state height at most `h₀ + 1`, or `J` is an entry block on the honest chain from `s₀` at a
slot `s_a` whose update ran by `t` (some validator ticked to `M.supportCutoff S.C (s_a + 1)` at a step at
a time at most `t`).

Why: `J` and its height are those of the chain state of a held block (`CachesWitnessed`);
Lemma 66 gives the justification certificate at that height on that block's chain, and past
`h₀ + 1` `justified_entry_of_cert` names the slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the validator.

Read aloud: a justified block is either from before the first opening's action time or the
honest chain's own entry at its height, confirmed by then.

Roots name blocks until `t`: `justified_entry_of_cert` at `t`. -/
theorem justified_old_or_entry (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t h₀ : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ A.corruptedAtTime x t) :
    (M.chainStateOf S.C (x.stateBefore t w).justified).h ≤ h₀ + 1 ∨
      ∃ s_a : ℕ, (∃ (k : ℕ) (u : V), x.time k ≤ t ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
        OnHonestChainAt M S A x s₀ s_a (x.stateBefore t w).justified ∧
        IsEntry M S.C (x.stateBefore t w).justified := by
  obtain ⟨⟨D, hDT, hDJ, -⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t w
  rw [hDJ]
  by_cases h0 : (M.chainStateOf S.C D).h_j = 0
  · left
    rw [((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 h0, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F)]
    exact Nat.le_add_left 1 h₀
  · have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := Nat.one_le_iff_ne_zero.mpr h0
    obtain ⟨hcert, hJD, hJh⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
    by_cases hle : ((M.chainStateOf S.C D).h_j : ℕ) ≤ h₀ + 1
    · left
      rw [hJh]
      exact hle
    · right
      exact (justified_entry_of_cert M F U Fx) S A x R s₀ t h₀ w D _ _ E hRoots hAdvQ hOld hw
        hDT hJD hcert (Nat.lt_of_not_le hle)

/-- **The finalized block is witnessed by a held block.** At every time, `w`'s finalized block
before `t` is the genesis block, or `w` holds a block `D` whose chain state finalized it, at a
finalization height at least `1`.

Why: the finalized block is the finalized block of the chain state of a held block
(`finalizedFromChain_of_exec`), and a chain state with finalization height `0` finalized the
genesis block.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the
  validator.

Read aloud: a validator's finalized block is the genesis block or was finalized by the chain state
of a block it holds. -/
theorem finalized_witnessed (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (w : V) :
    (x.stateBefore t w).finalized = Block.genesis ∨
      ∃ D ∈ (x.stateBefore t w).tree, (M.chainStateOf S.C D).F = (x.stateBefore t w).finalized ∧
        1 ≤ (M.chainStateOf S.C D).h_F := by
  obtain ⟨B, hB, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E (x.stepBefore t) w
  have hSt : x.stateBefore t w = x.st (x.stepBefore t) w := rfl
  rw [hSt]
  by_cases h0 : (M.chainStateOf S.C B).h_F = 0
  · left
    rw [hF]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C B h0
  · exact Or.inr ⟨B, hB, hF.symm, Nat.one_le_iff_ne_zero.mpr h0⟩

/-- **The finalized block is old, or an entry of the honest chain confirmed by `t`.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a quorum ever corrupted
up to `t`, with every honest attestation sent before the support cutoff of slot `s₀ + 1` at a
height at most `h₀ + 1`: when `w` is honest at `t`, its finalized block before `t` has
chain-state height at most `h₀ + 1`, or it is an entry block on the honest chain from `s₀` at a
slot `s_a` whose update ran by `t`.

Why: `finalized_witnessed` gives the held block `D` that finalized it; Lemma 66's third conjunct
gives a justification certificate at the finalization height for it on `D`'s chain; then as
`justified_old_or_entry`. The genesis block has height `1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the validator.

Read aloud: a finalized block is from before the first opening's action time or the honest
chain's own entry at its height.

Roots name blocks until `t`: `justified_entry_of_cert` at `t`. -/
theorem finalized_old_or_entry (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t h₀ : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ A.corruptedAtTime x t) :
    (M.chainStateOf S.C (x.stateBefore t w).finalized).h ≤ h₀ + 1 ∨
      ∃ s_a : ℕ, (∃ (k : ℕ) (u : V), x.time k ≤ t ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
        OnHonestChainAt M S A x s₀ s_a (x.stateBefore t w).finalized ∧
        IsEntry M S.C (x.stateBefore t w).finalized := by
  rcases (finalized_witnessed M F) S A x R E t w with hg | ⟨D, hDT, hDF, h1⟩
  · left
    rw [hg, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F)]
    exact Nat.le_add_left 1 h₀
  · rw [← hDF]
    obtain ⟨hcert, -, hFD, hFh⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 h1
    by_cases hle : ((M.chainStateOf S.C D).h_F : ℕ) ≤ h₀ + 1
    · left
      rw [hFh]
      exact hle
    · right
      exact (justified_entry_of_cert M F U Fx) S A x R s₀ t h₀ w D _ _ E hRoots hAdvQ hOld hw
        hDT hFD hcert (Nat.lt_of_not_le hle)

/-- **A `head_height_floor` past a height is a held block reaching past it, through an old
certificate or through the honest chain's entry.** Under unforgeability, roots naming blocks,
permanent corruption and fewer than a quorum ever corrupted up to `t`, with every honest
attestation sent before the support cutoff of slot `s₀ + 1` at a height at most `h₀ + 1`: when
`w`, honest at `t`, has its `head_height_floor` before `t` greater than `h`, `w` holds a block `Z`
of chain-state height at least `h + 1`, and `h ≤ h₀ + 1`, or the entry `E` of `Z`'s chain at the
height `h` is an entry block on the honest chain from `s₀` at a slot `s_a` whose update ran by
`t`.

Why: `head_height_floor` is at most the greatest chain-state height of `w`'s tree, the height of a
held block; past a height `h ≥ h₀ + 2` that block's chain carries a progress certificate at `h`
(Lemma 67) naming the honest chain's entry there at a slot whose update ran by `t`
(`cert_entry_at_slot`, with the roots naming blocks).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the validator; `h`: the height.

Read aloud: past a height at least `h₀ + 2`, a block of the greatest chain-state height `w` holds
passed that height through the honest chain's own entry there.

Roots name blocks until `t`: the proof compares the entry `T_h` of a block's chain, held by `w`
at the step before `t`, with the entry of the honest chain at a slot whose update ran by then. -/
theorem headHeightFloorPast_old_or_entry (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t h₀ : ℕ) (w : V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ A.corruptedAtTime x t)
    (hEvent : HeadHeightFloorPastAt M S A x w t h) :
    ∃ Z ∈ (x.stateBefore t w).tree, h + 1 ≤ (M.chainStateOf S.C Z).h ∧
      (h ≤ h₀ + 1 ∨
        ∃ (E : Block V) (s_a : ℕ), E.AncestorEq Z ∧ IsEntry M S.C E ∧
          (M.chainStateOf S.C E).h = h ∧ (∃ (k : ℕ) (u : V), x.time k ≤ t ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
          OnHonestChainAt M S A x s₀ s_a E) := by
  unfold HeadHeightFloorPastAt at hEvent
  set j := x.stepBefore t with hjdef
  have hjt : x.time j ≤ t := (time_stepBefore_le M) x R E t
  have hwj : w ∉ A.corrupted j := (not_mem_corrupted_of_le_time M) x R E hw (by exact_mod_cast hjt)
  have hAdvQj : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time j) (M.supportCutoff S.C (s₀ + 1))) :=
    (fun X hX => hAdvQ X (fun v hv => let ⟨t'', h1, h2⟩ := hX v hv;
      ⟨t'', le_trans h1 (max_le_max hjt le_rfl), h2⟩))
  have hSt : x.stateBefore t w = x.st j w := rfl
  obtain ⟨-, ⟨Z, hZT, hZh⟩, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t w
  have hfl : (M.head_height_floor (x.stateBefore t w) : ℕ) ≤ (hMax M S.C (x.stateBefore t w) : ℕ) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X _
      (lem11_node_invariant M F S A x R E j w hwj).1
  have hZ : h + 1 ≤ (M.chainStateOf S.C Z).h := by
    rw [hZh]
    exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hEvent hfl)
  refine ⟨Z, hZT, hZ, ?_⟩
  by_cases hle : (h : ℕ) ≤ h₀ + 1
  · exact Or.inl hle
  · right
    have hle' : h₀ + 1 < (h : ℕ) := Nat.lt_of_not_le hle
    obtain ⟨Y, hYZ, -, hYp, -, hTY, hcert⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Z h
        (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left 1 h₀) hle')) (Nat.lt_of_succ_le hZ)
    rw [hSt] at hZT
    have hYT : Y ∈ (x.st j w).tree := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w Z Y hZT hYZ
    have hTT : (M.chainStateOf S.C Y.parent).T_h ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w Y _ hYT hTY
    obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, hEb, hEon, hEent, hEh, hroot⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀
      (h₀ + 1) j w Y (M.chainStateOf S.C Y.parent).T_h h E hAdvQj hOld hYT hcert hle'
    have hkt : x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) ≤ t :=
      le_trans ((time_mono M) x R hk.le) hjt
    -- the attester held the entry at its tick, a step before `j`: one root, so one block
    have hEq : (M.chainStateOf S.C Y.parent).T_h = Eb := hRoots _ _
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjt hTT)
      ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl hkt hEb) hroot
    refine ⟨Eb, s_a, ?_, hEent, hEh, ⟨_, uₐ, hkt, hl⟩, hEon⟩
    rw [← hEq]
    exact ancestorEq_trans hTY hYZ

/-! ## A window that is not stable -/

/-- **A saved confirmation was held by its saver, and compatible with its finalized block, when the saver ticked to the support cutoff of its slot.**
When `v` is active from the duty window's start of slot `s + 1` up to its tick to the support cutoff
of slot `s + 1`, and the state that tick leaves has `X` saved as the confirmation of slot `s`, then
`v` ticked to the support cutoff of slot `s`, held `X` in the state that tick read, and its finalized
block there was compatible with `X`.

Why: `v` is active at every step from `ΔClockAhead` before the support cutoff of slot `s` up to its
tick to the support cutoff of slot `s + 1` (`tick_window_of_activeThroughoutToTick_int`, the duty
window's start being more than both clock bounds before that time, `hSkew`), so it ticks to the
support cutoff of slot `s` (`tick_of_active`), at a step before its tick to the support cutoff of
slot `s + 1` (the two are four delays apart). The update saved `X` because it passed the eligibility
test, so `X` has an early supporter at `v`'s tick input to the support cutoff of slot `s + 1`
(Lemma 36, the votes there stamped before that cutoff, `pool_vote_late_of_tick`), whose vote resolved
strictly before `S.C.t_ s + 2 · S.C.Δ`, the support cutoff of slot `s`; its head block, `X` or a
descendant of `X`, is stamped before that clock value, so held at `v`'s tick to it
(`mem_T_tick_of_blockStamp_lt`), and so is `X`, an ancestor of it. The head is in the frame's tree at
the later tick, so a descendant of `v`'s finalized block then, and of the earlier one: `X` and that
finalized block are both ancestors of the head, so compatible.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of the confirmation;
  `v`: the saver; `X`: the confirmation.

Read aloud: a validator held its confirmation of slot `s` when its clock reached the support cutoff
of slot `s`, and its finalized block then was compatible with it. -/
theorem saved_confirmation_held_compatible_supportCutoff (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V) (X : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to its
    -- support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v`'s state right after that cutoff has `X` saved as the confirmation of slot `s`
    (hX : (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some X) :
    x.lbl (x.tickStep v (M.supportCutoff S.C s)) = Event.tick v (M.supportCutoff S.C s) ∧
      X ∈ (x.tickInput v (M.supportCutoff S.C s)).tree ∧
      (x.tickInput v (M.supportCutoff S.C s)).finalized.compatible X = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv₂ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc₁ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s
  have hdle := (duty_window_start_le_real M F U) S (s + 1)
  -- the two support cutoffs, four delays apart, as real numbers
  have hcc : (M.supportCutoff S.C (s + 1) : ℝ) = (M.supportCutoff S.C s : ℝ) + 4 * Δ S := by
    have : M.supportCutoff S.C (s + 1) = M.supportCutoff S.C s + 4 * Δ S := by omega
    rw [this]; push_cast; ring
  have hdc : ((M.dutyWindowStart S.C (s + 1) : ℕ) : ℝ) + 2 * Δ S ≤ (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.dutyWindowStart S.C (s + 1) + 2 * Δ S ≤ M.supportCutoff S.C s by omega)
  -- `v`'s tick `k'` to the support cutoff of slot `s + 1`, active from `ΔClockAhead` before the support cutoff of slot `s`
  obtain ⟨k', hk', hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hk'a := (E.tick_active k' v _ hk').2.1
  have hvk' : v ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
  -- a step at a real time at most `ΔClockBehind` after the support cutoff of slot `s` is at or before `k'`
  have hbefore : ∀ i : ℕ, x.time i ≤ (M.supportCutoff S.C s : ℝ) + ΔClockBehind → i ≤ k' := by
    intro i hi
    by_contra hik
    have hm := (time_mono M) x R (Nat.lt_of_not_le hik).le
    linarith
  -- `v` ticks to the support cutoff of slot `s` at a step `k₀`, before `k'`
  have hc1 : 1 ≤ M.supportCutoff S.C s := by omega
  obtain ⟨k₀, hk₀, hk₀a, hk₀b⟩ := E.tick_of_active (M.supportCutoff S.C s) hc1 v
    (fun i hi1 hi2 => hwin i hi1 (hbefore i hi2))
  have hk₀k' : k₀ ≤ k' := hbefore k₀ hk₀b
  have hti : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k' v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk']
  have hts₀ : x.tickStep v (M.supportCutoff S.C s) = k₀ := (tickStep_eq_of_lbl M) x E hk₀
  have hti₀ : x.tickInput v (M.supportCutoff S.C s) = x.st k₀ v := by
    unfold Trace.tickInput; rw [hts₀]
  -- the update `v`'s tick to the support cutoff of slot `s + 1` ran, and the confirmation it saved
  have hAw := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (s + 1))
  obtain ⟨n'', sent, hrun, hAwake, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R s v E hk' hAw
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n'' sent hrun hAwake
  have hX' : M.savedConfirmation n'' s = some X := by rw [← hsave]; exact hX
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hRootsΦv : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  have hwin₂ : ∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ k' →
      v ∈ A.active j := fun j hj hjk => hwin j (by linarith) hjk
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      X X hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k' hk' hwin₂)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hX') (ancestorEq_refl X)
  simp only [Nat.add_sub_cancel] at hSup hElig
  obtain ⟨u, hu⟩ : Sup.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨vote, -, -, ⟨H, hHΦ, hroot, hXH⟩, ⟨y, hy, hyb⟩, -⟩ := hSup u hu
  obtain ⟨y', hyy', hyc⟩ := (GoldilocksCorrectness.Proofs.Routines.occurrenceBefore_eq_true_iff _ _).1 hyb
  cases hyy'
  -- the vote resolves at the later of its stamp and the stamp of the block its head names, which
  -- is `H` (roots name blocks in the frame's tree)
  obtain ⟨τv, τH, H', -, hH'Φ, hroot', -, hτH, hy⟩ := hy
  obtain rfl : H = H' := hRootsΦv H hHΦ H' hH'Φ (hroot.trans hroot'.symm)
  have hHT : H ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).1
  have hcast : ((((M.supportCutoff S.C s : ℕ) : Int)) : Stamp) =
      ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
  have hτlt : τH < ((((M.supportCutoff S.C s : ℕ) : Int)) : Stamp) := by
    rw [hcast]; exact lt_of_le_of_lt (by rw [hy]; exact le_max_right _ _) hyc
  have hHc : H ∈ (x.st k₀ v).tree :=
    (mem_T_tick_of_blockStamp_lt M F) x R E hk₀ hvk' (by rw [← hti]; exact hHT) (by rw [← hti]; exact hτH) hτlt
  refine ⟨by rw [hts₀]; exact hk₀, ?_, ?_⟩
  · rw [hti₀]
    exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v H X hHc hXH
  -- `v`'s finalized block at `k₀` is an ancestor of the one at `k'`, which is an ancestor of `H` (`H` is in
  -- the frame's tree), as `X` is
  have hFH : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq H :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).2
  rw [hti] at hFH
  have hFF := (F_ancestorEq_of_le M F) x R E v hk₀k'
  rw [hti₀]
  exact (compatible_iff _ _).2 (GoldilocksCorrectness.Proofs.Routines.ancestorEq_compatible (ancestorEq_trans hFF hFH) hXH)

/-- **A saved confirmation was held by its saver when it ticked to the support cutoff of its slot.**
When `v` is active from the duty window's start of slot `s + 1` up to its tick to the support cutoff
of slot `s + 1`, and the state that tick leaves has `X` saved as the confirmation of slot `s`, then
`v` held `X` in the state its tick to the support cutoff of slot `s` read.

Why: `saved_confirmation_held_compatible_supportCutoff`, its second conjunct.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of the confirmation;
  `v`: the saver; `X`: the confirmation.

Read aloud: a validator held its confirmation of slot `s` when its clock reached the support cutoff
of slot `s`. -/
theorem saved_confirmation_mem_T_supportCutoff (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V) (X : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to its
    -- support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v`'s state right after that cutoff has `X` saved as the confirmation of slot `s`
    (hX : (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some X) :
    X ∈ (x.tickInput v (M.supportCutoff S.C s)).tree :=
  ((saved_confirmation_held_compatible_supportCutoff M F U) S A x R s v X E hSkew hv hX).2.1

/-- **A failed chain step relative to a confirmation, written out.** Under synchrony from one delay
or one sync delay before the support cutoff of slot `σ`: when `v`, an updater of slot `σ`, saved `X`
as its confirmation of slot `σ ≤ s₁` and is active for one sync delay from that window's start, `w`
ticks to the vote time of slot `s₁ + 1` and is active at every step from that window's start up to
that tick, and `StepFrameAt M S Sched x X s₁ w` fails, then `w`'s root at its tick to the vote time
of slot `s₁ + 1` conflicts with `X`; or that root is `X` or an ancestor of `X`, `w` holds `X` then,
and no viable head of `w`'s voter tree of slot `s₁ + 1` is `X` or a descendant of `X`; or `w`'s
finalized block at its tick to the support cutoff of slot `s₁ + 2` conflicts with `X`.

Why: the three conjuncts of `StepFrameAt` negated. In the second case `v` held `X` at its tick to
the support cutoff of slot `σ`, its finalized block there compatible with `X`
(`saved_confirmation_held_compatible_supportCutoff`); `w` ticks to that cutoff and to one delay
after it (`tick_of_active`, both before its tick to the vote time); `w`'s finalized block at the
later tick is an ancestor of its finalized block at the vote tick, so of its root, so of `X`; so `X`
reaches `w` by that tick, and
`mem_T_mono` carries it to `w`'s tick to the vote time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `σ ≤ s₁`: the slot of the confirmation and the slot of the step;
  `v`: the saver; `w`: the member; `X`: the confirmation.

Roots name blocks up to every validator's tick to `M.supportCutoff S.C σ + Δ S`: the
proof takes `X`, which `v` holds at its tick to the support cutoff of slot `σ`, as reaching `w` by
`w`'s tick to one delay later (`block_at_tick_of_held_tick`), whose real time can be up to
`ΔClockBehind` after that clock value, and carries it to `w`'s tick to the vote time (`mem_T_mono`).

Read aloud: a failed `StepFrameAt` relative to a saved confirmation `X` is a root conflicting with
`X`, a voter tree with no viable head on `X`'s chain, or a finalized block conflicting with `X`. -/
theorem stepFrameAt_fail_cases (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST σ s₁ : ℕ) (v w : V) (X : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    -- roots name blocks up to every validator's tick to one delay after the support cutoff of slot `σ`
    (hRoots : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C σ + Δ S) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- the window of one delay or one sync delay before the support cutoff of slot `σ` is in the
    -- synchronous period
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ)
    (hσ : σ ≤ s₁)
    -- `v` is an updater of slot `σ`: active from the duty window's start of slot `σ + 1` up to its
    -- tick to the support cutoff of slot `σ + 1`
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (M.supportCutoff S.C (σ + 1)))
    -- `v` is active for one sync delay from one delay or one sync delay before the support cutoff of
    -- slot `σ`
    (hv₀ : v ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the vote time of slot `s₁ + 1` and is active at every step from one delay or one
    -- sync delay before the support cutoff of slot `σ` up to that tick
    (hw : ∃ kV : ℕ, x.lbl kV = Event.tick w (M.voteTime S.C (s₁ + 1)) ∧
      ∀ i : ℕ, ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kV → w ∈ A.active i)
    -- `v`'s state right after the support cutoff of slot `σ + 1` has `X` saved for slot `σ`
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X)
    (hFail : ¬ StepFrameAt M S A x X s₁ w) :
    RootIncompatibleAtTick M S A x w (M.voteTime S.C (s₁ + 1)) X ∨
      ((M.get_fc_root (x.tickInput w (M.voteTime S.C (s₁ + 1)))).AncestorEq X ∧
        X ∈ (x.tickInput w (M.voteTime S.C (s₁ + 1))).tree ∧
        ¬ ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₁ + 1)))
            (S.C.t_ ((s₁ + 1) - 1) + 3 * S.C.Δ) (s₁ + 1) W ∧
          W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₁ + 1)))).viable_heads ∧
          X.AncestorEq W) ∨
      FinalizedIncompatibleAtTick M S A x w (M.supportCutoff S.C (s₁ + 2)) X := by
  unfold StepFrameAt at hFail
  have hfc := (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)
    (x.tickInput w (M.voteTime S.C (s₁ + 1)))
  by_cases h1 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₁ + 1)))).fc_root.compatible X = true
  swap
  · left
    unfold RootIncompatibleAtTick
    rw [← hfc]
    exact h1
  by_cases h3 : (x.tickInput w (M.supportCutoff S.C (s₁ + 2))).finalized.compatible X = true
  swap
  · right; right
    exact h3
  -- the second conjunct fails
  right; left
  have h2 := fun h2 => hFail ⟨h1, h2, h3⟩
  obtain ⟨hroot, hno⟩ := Classical.not_imp.1 h2
  have hroot' : (M.get_fc_root (x.tickInput w (M.voteTime S.C (s₁ + 1)))).AncestorEq X := by
    rw [← hfc]; exact hroot
  refine ⟨hroot', ?_, hno⟩
  -- `w` holds `X`: the saver held it at its tick to the support cutoff of slot `σ`
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨-, hc0, -, hs0, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvs, -, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  have hsm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show σ + 1 ≤ s₁ + 1 by omega)
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = M.supportCutoff S.C σ - max (Δ S) Δs := ⟨_, rfl⟩
  rw [← ha_def] at hv₀ hw
  obtain ⟨kV, hkV, hwV⟩ := hw
  have hkVt := E.tick_active kV w _ hkV
  -- `w` ticks, before its tick to the vote time, to every clock value from one delay after `a` to one
  -- delay before the vote time
  have htick : ∀ t : ℕ, a + Δ S ≤ t → t + Δ S ≤ M.voteTime S.C (s₁ + 1) →
      ∃ k, x.lbl k = Event.tick w t ∧ k < kV := by
    intro t h1 h2
    have h1R : ((a : ℕ) : ℝ) + Δ S ≤ (t : ℝ) := by exact_mod_cast h1
    have h2R : (t : ℝ) + Δ S ≤ ((M.voteTime S.C (s₁ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    have hlt : ∀ i, x.time i ≤ t + ΔClockBehind → i < kV := fun i hi =>
      (lt_of_time_lt M) x R (by linarith [hkVt.2.1])
    obtain ⟨k, hk, -, hk2⟩ := E.tick_of_active t (by omega) w fun i hi1 hi2 =>
      hwV i (by linarith) (hlt i hi2).le
    exact ⟨k, hk, hlt k hk2⟩
  obtain ⟨kR, hkR, hkRV⟩ := htick (M.supportCutoff S.C σ + Δ S) (by omega) (by omega)
  obtain ⟨k₂, hk₂, -⟩ := htick (M.supportCutoff S.C σ) (by omega) (by omega)
  -- the saver's tick to the support cutoff of slot `σ`, where it holds `X`
  obtain ⟨hkU, hXT, hFC⟩ :=
    (saved_confirmation_held_compatible_supportCutoff M F U) S A x R σ v X E hSkew hv hX
  have hkUt := E.tick_active _ v _ hkU
  have hsa : x.stepBefore a ≤ x.tickStep v (M.supportCutoff S.C σ) := by
    by_contra hc
    have h := ((lt_stepBefore_iff M) x R E).1
      (show x.tickStep v (M.supportCutoff S.C σ) < x.stepBefore a by omega)
    have h' := htime (Nat.le_succ (x.tickStep v (M.supportCutoff S.C σ)))
    have haR : ((a : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) := by
      exact_mod_cast (show a + Δ S ≤ M.supportCutoff S.C σ by omega)
    linarith [hkUt.2.1]
  have hFa : (x.st (x.stepBefore a) v).finalized.compatible X = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both ((F_ancestorEq_of_le M F) x R E v hsa) (ancestorEq_refl X) hFC
  -- `X`'s slot is at most `σ`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslotc : S.C.slot ((M.supportCutoff S.C σ : ℕ) : Int) = σ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have huU : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C σ)) := E.not_mem_corrupted_of_tick hkU
  have hXs : X.slot ≤ σ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E huU hXT
    rw [← hslotc]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
      (by exact_mod_cast E.clockValue_le_of_set huU (Or.inl hkU)))
  have hXc₂ : M.slotStart S.C X.slot ≤ M.supportCutoff S.C σ :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hXs)
      (by omega)
  -- `w`'s finalized block at its tick to one delay after that cutoff is an ancestor of `X`: of its
  -- finalized block at the vote tick, of the root there, of `X`
  have hVin : x.tickInput w (M.voteTime S.C (s₁ + 1)) = x.st kV w := by
    show x.st (x.tickStep w (M.voteTime S.C (s₁ + 1))) w = x.st kV w
    rw [(tickStep_eq_of_lbl M) x E hkV]
  have hrootV := hroot'
  rw [hVin] at hrootV
  have hFw : (x.st kR w).finalized.compatible X = true := by
    have hF1 := (F_ancestorEq_of_le M F) x R E w hkRV.le
    have hF2 := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F)
      S A x R E kV w
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hF1 (ancestorEq_trans hF2 hrootV)))
  rw [hVin]
  by_cases hg : X = Block.genesis
  · rw [hg]
    exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
  have hXR := (block_at_tick_of_held_tick M F U) S A x R GST (M.supportCutoff S.C σ + Δ S)
    (M.supportCutoff S.C σ) (x.tickStep v (M.supportCutoff S.C σ)) a (M.supportCutoff S.C σ + Δ S)
    (M.supportCutoff S.C σ) kR k₂ v w X (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
    (hRoots kR w hkR) hParent (by omega) (by omega) le_rfl le_rfl hv₀ hkU hXT hFa hg hkR
    (fun i hi hik => hwV i hi (le_trans hik hkRV.le)) hk₂ le_rfl hXc₂ hFw
  exact (mem_T_mono M F) x R E w hkRV.le hXR

/-- **A window of real times inside the phase, for a validator honest to its end.** When every
validator outside the adversary set in a configuration in force at a time of `[tGAT, tAwakeEnd]` is awake
in it, a validator outside the adversary set at every step whose time is at most `b`, with `b ≤ tAwakeEnd`
and `tGAT` at most the larger of `a` and `0`, is active in every configuration in force at some time of
`[a, b]`.

Why: such a configuration is that of a step `i` with `x.time i ≤ b` and `a ≤ x.time (i + 1)`; the time
`x.time (i + 1)` is also at least `0`, so at least `tGAT`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `tGAT`, `tAwakeEnd`: the phase; `a`, `b`: the window; `v`:
  the validator.

Read aloud: a validator honest through a window of the phase is active through it. -/
theorem mem_activeThroughout_of_hAwake_real {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {tGAT tAwakeEnd : ℕ}
    -- every validator outside the adversary set in a configuration in force at a time of `[tGAT, tAwakeEnd]` is awake in it
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    {a b : ℝ} (ha : (tGAT : ℝ) ≤ max a 0) (hb : b ≤ tAwakeEnd) {v : V}
    -- `v` is outside the adversary set at every step whose time is at most `b`
    (hv : ∀ i : ℕ, x.time i ≤ b → v ∉ A.corrupted i) :
    v ∈ A.activeThroughout x a b := by
  refine Activity.mem_activeThroughout.2 fun i h1 h2 => ?_
  have hci : v ∉ A.corrupted i := hv i h1
  have h0 := (time_nonneg M) x R (i + 1)
  exact Activity.mem_active.2 ⟨hAwake i v (le_trans h1 hb) (le_trans ha (max_le h2 h0)) hci, hci⟩

/-- **The times of a window slot.** With `Δs` and three delays fitting in the `4 Δ k` before a
vote time, `GST ≤ tGAT`, `tGAT` at most the duty window's start of slot `s_w`, the support cutoff of slot
`s' + 1` at most `tAwakeEnd`, and `s_w + k − 1 ≤ σ ≤ s₁ < s'`: the inequalities between the slot times
of `σ`, `σ + 1`, `σ + 2`, `s₁ + 1`, `s₁ + 2` and `s' − 1` that `frontWindow_stepFrame_fail_cases` reads.

Why: the uniform schedule (slot `s` starts at `4 Δ s`, its vote time and support cutoff one and two
delays later) and the duty window's start (`4 Δ k − Δ` before the slot's start, or `0`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `GST`, `tGAT`, `tAwakeEnd`: the synchronous time and the phase; `s_w`, `s'`: the
  window; `σ`, `s₁`: the slots; `Δs`: the sync delay.

Read aloud: the windows the step-frame case reads fit inside the phase. -/
theorem frontWindow_times (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (GST tGAT tAwakeEnd s_w s' σ s₁ Δs : ℕ)
    (hΔsN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k) (hGST : GST ≤ tGAT)
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w) (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    (hσ1 : s_w + S.C.k - 1 ≤ σ) (hσ2 : σ ≤ s₁) (h2 : s₁ < s') :
    tGAT + max (Δ S) Δs ≤ M.supportCutoff S.C σ ∧
    GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ ∧
    (tGAT + 4 * Δ S ≤ M.dutyWindowStart S.C (σ + 1) ∨ tGAT = 0) ∧
    M.dutyWindowStart S.C (σ + 1) ≤ M.supportCutoff S.C σ - max (Δ S) Δs ∧
    M.dutyWindowStart S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 1) ∧
    M.supportCutoff S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 2) ∧
    M.supportCutoff S.C σ - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 2) ∧
    M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd ∧
    M.voteTime S.C (s₁ + 1) + Δ S ≤ M.supportCutoff S.C (s₁ + 2) ∧
    M.supportCutoff S.C (s₁ + 2) ≤ tAwakeEnd ∧
    M.supportCutoff S.C σ - max (Δ S) Δs + Δ S ≤ M.voteTime S.C (s₁ + 1) ∧
    1 ≤ M.voteTime S.C (s₁ + 1) ∧
    M.supportCutoff S.C σ ≤ M.supportCutoff S.C (s' - 1) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hdm := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S (show s_w ≤ σ by omega)
  have hdσ := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S σ
  have hdσ₁ := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (σ + 1)
  have hssσ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ
  have hvσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hc₀ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have hc₁ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv₁ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S σ
  have hv₂ : M.voteTime S.C (σ + 2) = M.voteTime S.C (σ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (σ + 1)
  have hvs := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (show σ + 1 ≤ s₁ + 1 by omega)
  have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₁ + 2 ≤ s' + 1 by omega)
  have hcσ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ + 2 ≤ s' + 1 by omega)
  have hcv := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  have hcw := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₁ + 1 ≤ s₁ + 2 by omega)
  have hcR := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ ≤ s' - 1 by omega)
  have hkσ := Nat.mul_le_mul_left (4 * Δ S) (show S.C.k - 1 ≤ σ by omega)
  have hk1 : 4 * Δ S * (S.C.k - 1) + 4 * Δ S = 4 * Δ S * S.C.k := by
    rw [← Nat.mul_succ]; congr 1; omega
  have hσ1' : 4 * Δ S * (σ + 1) = 4 * Δ S * σ + 4 * Δ S := by ring
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  generalize max (Δ S) Δs = m at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, hcR⟩

/-- **A failed step frame at a window slot, from the phase.** In the setting of
`frontWindowStable_fail_event`: when a member `v` of slot `σ + 1` saved `X` for slot `σ` at its tick to
the support cutoff of slot `σ + 1`, a member `w` of slot `s₁ + 1` (with `σ ≤ s₁ < s'`) fails
`StepFrameAt` for `X` at `s₁`, and both are honest at the support cutoffs of slots `σ + 2` and `s₁ + 2`:
`w`'s root conflicts with `X`, or it is `X` or an ancestor of `X` and `w` holds `X` with no viable
head on `X`'s chain, or `w`'s finalized block conflicts with `X`.

Why: `stepFrameAt_fail_cases`, with `v` an updater of slot `σ` and active for one sync delay from one
delay or one sync delay before the support cutoff of slot `σ`, and `w` ticking to the vote time of slot
`s₁ + 1` and active from then to that tick; all from `hAwake` over windows inside the phase
(`mem_activeThroughout_of_hAwake_real`), the windows' starts at or after `tGAT` by the duty window of
slot `s_w` and `hΔs`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its facts; `GST`, `tGAT`,
  `tAwakeEnd`: the synchronous time and the phase; `s_w`, `s'`: the window; `σ`, `s₁`: the slots;
  `v`, `w`: the members; `X`: the confirmation.

Read aloud: a member that fails the step frame at a window slot does so in one of the three ways. -/
theorem frontWindow_stepFrame_fail_cases (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s_w s' σ s₁ : ℕ) (v w : V)
    (X : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most one delay after the
    -- support cutoff of slot `s' - 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C (s' - 1) + Δ S → RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w) (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    (hσ1 : s_w + S.C.k - 1 ≤ σ) (hσ2 : σ ≤ s₁) (h2 : s₁ < s')
    -- `v` is honest at the support cutoff of slot `σ + 2`, `w` at that of slot `s₁ + 2`
    (hvH : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2)))
    (hwH : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 2)))
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X)
    (hst : ¬ StepFrameAt M S A x X s₁ w) :
    RootIncompatibleAtTick M S A x w (M.voteTime S.C (s₁ + 1)) X ∨
      ((M.get_fc_root (x.tickInput w (M.voteTime S.C (s₁ + 1)))).AncestorEq X ∧
        X ∈ (x.tickInput w (M.voteTime S.C (s₁ + 1))).tree ∧
        ¬ ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₁ + 1)))
            (S.C.t_ ((s₁ + 1) - 1) + 3 * S.C.Δ) (s₁ + 1) W ∧
          W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₁ + 1)))).viable_heads ∧
          X.AncestorEq W) ∨
      FinalizedIncompatibleAtTick M S A x w (M.supportCutoff S.C (s₁ + 2)) X := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔsN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  obtain ⟨hGσ, hGSTσ, hGd₀, hdc, hab, hc12, hc0s, hc2E, hvc, hcwE, hvt, hv1, hcR⟩ :=
    (frontWindow_times M F U) S GST tGAT tAwakeEnd s_w s' σ s₁ Δs hΔsN hGST hsw hEnd hσ1 hσ2 h2
  have hskew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ) := hSkew
  have hΔ0 : (0 : ℝ) ≤ (Δ S : ℝ) := Nat.cast_nonneg _
  -- `tGAT` is at most the duty window's start of slot `σ + 1`, less the clock-ahead bound, or `0`
  have hGd : (tGAT : ℝ) ≤ max ((M.dutyWindowStart S.C (σ + 1) : ℝ) - ΔClockAhead) 0 := by
    rcases hGd₀ with hd | hd
    · have : ((tGAT + 4 * Δ S : ℕ) : ℝ) ≤ (M.dutyWindowStart S.C (σ + 1) : ℝ) := by exact_mod_cast hd
      push_cast at this
      exact le_max_of_le_left (by linarith)
    · rw [hd, Nat.cast_zero]
      exact le_max_right _ _
  -- `v`, a member of slot `σ + 1`: active from the clock-ahead bound before the duty window's start
  -- of slot `σ + 1` to the support cutoff of slot `σ + 2`
  have hvW : v ∈ A.activeThroughout x ((M.dutyWindowStart S.C (σ + 1) : ℝ) - ΔClockAhead)
      (M.supportCutoff S.C (σ + 2)) :=
    (mem_activeThroughout_of_hAwake_real M F) R hAwake hGd (by exact_mod_cast hc2E)
      (fun i hi => Activity.not_mem_corruptedAtTime.1 hvH i (by exact_mod_cast hi))
  have hc12R : (M.supportCutoff S.C (σ + 1) : ℝ) + ΔClockBehind ≤ (M.supportCutoff S.C (σ + 2) : ℝ) := by
    have : ((M.supportCutoff S.C (σ + 1) + Δ S : ℕ) : ℝ) ≤ (M.supportCutoff S.C (σ + 2) : ℝ) := by
      exact_mod_cast hc12
    push_cast at this
    linarith
  have hvU : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (M.supportCutoff S.C (σ + 1)) :=
    (mem_updaterAt_of_mem_activeThroughout M F U) R E hab
      (Activity.mem_activeThroughout_of_le le_rfl hc12R hvW)
  have hv₀ : v ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hvW
    · have : (M.dutyWindowStart S.C (σ + 1) : ℝ) ≤ ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) := by
        exact_mod_cast hdc
      linarith
    · exact_mod_cast hc0s
  -- `w`, a member of slot `s₁ + 1`: active from one delay or one sync delay before the support
  -- cutoff of slot `σ` to the clock-behind bound after the vote time of slot `s₁ + 1`; so it ticks
  -- to that vote time, at a step at a time at most that end
  have hb : (M.voteTime S.C (s₁ + 1) : ℝ) + ΔClockBehind ≤ (M.supportCutoff S.C (s₁ + 2) : ℝ) := by
    have : ((M.voteTime S.C (s₁ + 1) + Δ S : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s₁ + 2) : ℝ) := by
      exact_mod_cast hvc
    push_cast at this
    linarith
  have hwW : w ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      ((M.voteTime S.C (s₁ + 1) : ℝ) + ΔClockBehind) :=
    (mem_activeThroughout_of_hAwake_real M F) R hAwake
      (le_max_of_le_left (by exact_mod_cast (show tGAT ≤ M.supportCutoff S.C σ - max (Δ S) Δs from
        Nat.le_sub_of_add_le hGσ)))
      (le_trans hb (by exact_mod_cast hcwE))
      (fun i hi => Activity.not_mem_corruptedAtTime.1 hwH i (by exact_mod_cast (le_trans hi hb)))
  have hvtR : ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) + Δ S ≤ (M.voteTime S.C (s₁ + 1) : ℝ) := by
    have : (((M.supportCutoff S.C σ - max (Δ S) Δs + Δ S : ℕ)) : ℝ) ≤ (M.voteTime S.C (s₁ + 1) : ℝ) := by
      exact_mod_cast hvt
    push_cast at this
    linarith
  obtain ⟨kV, hkV, -, hkV2⟩ := E.tick_of_active (M.voteTime S.C (s₁ + 1)) hv1 w
    (fun i hi1 hi2 => Activity.mem_activeThroughout.1 hwW i hi2
      (by linarith [R.time_mono (Nat.le_succ i)]))
  have hwT : ∃ kV : ℕ, x.lbl kV = Event.tick w (M.voteTime S.C (s₁ + 1)) ∧
      ∀ i : ℕ, ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kV → w ∈ A.active i :=
    ⟨kV, hkV, fun i hi1 hi2 => Activity.mem_activeThroughout.1 hwW i (le_trans (R.time_mono hi2) hkV2)
      (le_trans hi1 (R.time_mono (Nat.le_succ i)))⟩
  exact (stepFrameAt_fail_cases M F U) S A x R GST σ s₁ v w X E hNet hSkew hRedeliver Sy
    (fun k u hl => hRoots k u _ hl (Nat.add_le_add_right hcR _)) hParent hGSTσ hσ2 hvU hv₀ hwT hX hst

/-- **A failure of `FrontWindowStable`, written out.** Under the member sets shrinking from one slot
to the next and every member of the set of a slot honest at the support cutoff of the next slot:
when `FrontWindowStable M S Sched x (Hon M) s_w s'` fails, one of four things happens, each at a
member `w` of a set `Hon M s₁` with `s_w + k − 1 ≤ s₁ ≤ s'`:

1. `w`, a member of `Hon M (s₁ + 1)` with `s₁ < s'`, has its root before `M.voteTime S.C (s₁ + 1)`
in conflict with a confirmation `X` a member saved for a slot from `s_w + k − 1` to `s₁`
   (`RootIncompatibleAt`);
2. or that root is `X` or an ancestor of such an `X`, `w` holds `X` then, and no block of `w`'s
   voter tree of slot `s₁ + 1` that is `X` or a descendant of `X` is a viable head;
3. or `w`'s finalized block before `M.supportCutoff S.C (s₁ + 2)` conflicts with such an `X`
   (`FinalizedIncompatibleAt`);
4. or, at `s₁ = s'`, `w`'s root before `M.voteTime S.C (s' + 1)` is `D` or an ancestor of `D` for no
   block `D` of a live lock entry of a member of `Hon M s'` and no confirmation `D` of slot `s' − 1`
   of a member of `Hon M s'` (`RootOffChainAt` at every such `D`).

Why: the two clauses of `FrontWindowStable` negated; the failure of the first is a failed
`StepFrameAt` (`stepFrameAt_fail_cases`), where `w` holds `X` in the second case by the delivery
of the saver's own copy.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase, in which every honest validator is
  awake; `s_w`: the slot the window is counted from; `s'`: its last slot; `Hon`: one member set
  per slot.

Read aloud: a window breaks at a member whose root or finalized block conflicts with a window
confirmation, whose frame finds no viable head on a confirmation's chain, or whose root is on no
family block's chain at the window's last slot.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' - 1) + Δ S`
: `stepFrameAt_fail_cases` at a slot `σ` at most `s' − 1`, whose roots premise is that
form at the clock value `M.supportCutoff S.C σ + Δ S`. -/
theorem frontWindowStable_fail_event (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most one delay after the
    -- support cutoff of slot `s' - 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C (s' - 1) + Δ S → RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from `tGAT` on; the window has at least `2k − 1` slots
    (hGST : GST ≤ tGAT) (hs' : s_w + 2 * S.C.k - 1 ≤ s')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    -- every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- the duty window of slot `s_w` starts at or after `tGAT`; the support cutoff of slot
    -- `s' + 1` is inside the phase
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w) (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    -- the window is not stable
    (hFail : ¬ FrontWindowStable M S A x Hon s_w s') :
    ∃ (s₁ : ℕ) (w : V), s_w + S.C.k - 1 ≤ s₁ ∧ s₁ ≤ s' ∧ w ∈ Hon s₁ ∧
      ((∃ X : Block V, WindowConfirmation M S A x Hon (s_w + S.C.k - 1) s₁ X ∧ s₁ < s' ∧
          w ∈ Hon (s₁ + 1) ∧
          (RootIncompatibleAtTick M S A x w (M.voteTime S.C (s₁ + 1)) X ∨
            ((M.get_fc_root (x.tickInput w (M.voteTime S.C (s₁ + 1)))).AncestorEq X ∧
              X ∈ (x.tickInput w (M.voteTime S.C (s₁ + 1))).tree ∧
              ¬ ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₁ + 1)))
                  (S.C.t_ ((s₁ + 1) - 1) + 3 * S.C.Δ) (s₁ + 1) W ∧
                W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₁ + 1)))).viable_heads ∧
                X.AncestorEq W) ∨
            FinalizedIncompatibleAtTick M S A x w (M.supportCutoff S.C (s₁ + 2)) X)) ∨
        (s₁ = s' ∧ ∀ D : Block V,
          ((∃ u ∈ Hon s', ∃ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
              M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
                ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
            ∃ v ∈ Hon s',
              (x.tickOutput v (M.supportCutoff S.C s')).savedConfirmation (s' - 1) = some D)
                  →
          RootOffChainAtTick M S A x w (M.voteTime S.C (s' + 1)) D)) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  unfold FrontWindowStable at hFail
  by_cases hc1 : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
      ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
        (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C →
        ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C s₁ w
  · -- clause 2 fails
    have hc2 : ¬ ∀ w ∈ Hon s', ∃ D : Block V,
        ((∃ u ∈ Hon s', ∃ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
            M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
              ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
          ∃ v ∈ Hon s',
            (x.tickOutput v (M.supportCutoff S.C s')).savedConfirmation (s' - 1) = some D) ∧
        (M.get_fc_root (x.tickInput w (M.voteTime S.C (s' + 1)))).AncestorEq D :=
      fun h => hFail ⟨hc1, h⟩
    push Not at hc2
    obtain ⟨w, hw, hD⟩ := hc2
    exact ⟨s', w, by omega, le_rfl, hw, Or.inr ⟨rfl, fun D hDf => hD D hDf⟩⟩
  · -- clause 1 fails
    push Not at hc1
    obtain ⟨s₁, h1, h2, σ, hσ1, hσ2, v, hv, X, hX, w, hw, hst⟩ := hc1
    have hw₀ : w ∈ Hon s₁ := hHonMono s₁ (by omega) h2 hw
    refine ⟨s₁, w, h1, by omega, hw₀, Or.inl ⟨X, ⟨σ, hσ1, hσ2, v, hv, hX⟩, h2, hw, ?_⟩⟩
    exact (frontWindow_stepFrame_fail_cases M F U) S A x R GST tGAT tAwakeEnd s_w s' σ s₁ v w X E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hGST hAwake hsw hEnd hσ1 hσ2 h2
      (hHon (σ + 1) (by omega) (by omega) v hv) (hHon (s₁ + 1) (by omega) (by omega) w hw) hX hst

end GoldilocksCorrectness.Record.Proofs.Executions

