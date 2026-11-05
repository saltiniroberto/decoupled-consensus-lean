module
public import GoldilocksCorrectness.Proofs.Executions.PeriodInductionCompat
public import GoldilocksCorrectness.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Proofs.Executions.AsyncHandover
public import GoldilocksCorrectness.Proofs.Executions.HealedTopUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo

@[expose] public section

/-! The audited statements are in
`Statements/Executions/AsyncResilienceStatements.lean`.

- `preceq_confirmedOf_of_record_and_F`: a confirmed tip extends `B` when the record does, is held,
  and the finalized block is compatible with `B` (promoted from
  `scratch/goldilocks_async/probe_outside_1.lean:104`, statement and proof unchanged);
- `F_compatible_of_caches`: the finalized block of caches compatible with `B` is compatible with `B`;
- `period_facts_from_handover`: at a step from the hand-over update on, the lock holders record `B` or a
  descendant of `B` and hold it, and every honest finalized block is compatible with `B`;
- `confirmedPersists_throughPeriod_until` (Lemma 105);
- `gst_le_voteTime_succ_of_top`: the top statement's premises put `GST` at or before the vote time
  of slot `s + 1` (promoted from `scratch/goldilocks_async/probe_ar4_replan.lean:127`, statement and
  proof unchanged);
- `confirmedPersists_asyncPeriod_until` (the asynchrony top statement);
- `confirmedPersists_asyncPeriod`, its corollary read forever.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_mono slot_le_of_supportCutoff_lt
  supportCutoff_eq supportCutoff_mono times_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

open GoldilocksCorrectness.Proofs.Routines (fg_to_ac_F)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

omit [Fintype V] [RootOrder] in
/-- **The confirmed tip extends `B` when the record does and the finalized block is compatible
with `B`.** For a node state `n`: when `B` is the record `n.A.latest_confirmed` or an ancestor of
it, the record is in `n`'s tree, and the finalized block `n.S.F` is compatible with `B`, then `B`
is the confirmed tip `confirmedOf n` or an ancestor of it.

Why: the confirmed tip is the record when the record is in the frame's tree, the finalized block
otherwise (`ac_confirmed_cases`). In the first case the record extends `B`. In the second the
finalized block is not an ancestor of the record (else the record, held in `n.S.T`, would be in the
frame's tree), so it is not `B` or an ancestor of `B` (which is an ancestor of the record): by
compatibility it is a descendant of `B`.

Promoted from `scratch/goldilocks_async/probe_outside_1.lean:104`, statement and proof unchanged.

The variables:
- `n`: the node state; `B`: the block.

Read aloud: whether the validator is awake or asleep, its confirmed tip extends `B` as long as its
record extends `B` and its finalized block is compatible with `B`. -/
theorem preceq_confirmedOf_of_record_and_F (n : NodeState V) (B : Block V)
    (hrec : B.AncestorEq n.A.latest_confirmed) (hT : n.A.latest_confirmed ∈ n.S.T)
    (hF : n.S.F.AncestorEq B ∨ B.AncestorEq n.S.F) :
    B.AncestorEq (confirmedOf n) := by
  unfold confirmedOf
  rcases GoldilocksCorrectness.Proofs.Routines.ac_confirmed_cases n.A (fg_to_ac n.S) with
    ⟨-, h⟩ | ⟨hout, h⟩
  · rw [h]; exact hrec
  · rw [h]
    have hFeq : (fg_to_ac n.S).F = n.S.F := fg_to_ac_F n.S
    rw [hFeq]
    rcases hF with hFB | hBF
    · exfalso
      exact hout ((mem_fg_to_ac_tree n.S _).2 ⟨hT, ancestorEq_trans hFB hrec⟩)
    · exact hBF

omit [RootOrder] in
/-- The finalized block of a node state whose caches are compatible with `B` is compatible with
`B`: it is the justified block or an ancestor of it, and the justified block is compatible with
`B`.

The variables:
- `S`: the setup; `B`: the block; `H`: the threshold; `n`: the node state. -/
theorem F_compatible_of_caches {S : Setup V} {B : Block V} {H : ℕ} {n : NodeState V}
    (hC : CachesCompatibleWith S B H n) : n.S.F.AncestorEq B ∨ B.AncestorEq n.S.F := by
  rcases hC.2.1 with hJB | hBJ
  · exact Or.inl (ancestorEq_trans hC.2.2.2.2 hJB)
  · exact ancestorEq_compatible hC.2.2.2.2 hBJ

/-- **The period's facts at a step from the hand-over update on.** Under the hypotheses `P` of the
period: at every step `j` at a time at least the hand-over update `c`, with roots naming blocks
among what honest validators hold up to `x[j].time`, every lock holder honest through `j` records
`B` or a descendant of `B` and holds its record, and every validator honest at `j` has its
finalized block compatible with `B`.

Why: after `c`, the second and third clauses of `PeriodInvCompatDueByCutoff`
(`period_inv_compat_all`). At `c`: the step `j` comes after the tick at `c` and at or before the
step `stepBefore x (c + 1)`; the record is the one there (`stateBefore_succ_keepsConfirmation`),
`B` by the hand-over facts, and the finalized block at `j` is an ancestor of the one there, whose
caches the hand-over facts make compatible with `B`.

The variables:
- `P`: the hypotheses of the period; `j`: the step. -/
theorem period_facts_from_handover {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (j : ℕ) (hj : supportCutoff S (s + 1) ≤ x[j].time)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time) :
    (∀ w ∈ updaterAt S Sched s, HonestThrough x j w →
      B.AncestorEq (x[j][w].st).A.latest_confirmed ∧
      (x[j][w].st).A.latest_confirmed ∈ (x[j][w].st).S.T) ∧
    (∀ u : V, u ∉ Sched.adv (x[j].time : Int) →
      (x[j][u].st).S.F.AncestorEq B ∨ B.AncestorEq (x[j][u].st).S.F) := by
  rcases Nat.lt_or_ge (supportCutoff S (s + 1)) x[j].time with hlt | hge
  · have hI := GoldilocksCorrectness.Proofs.Executions.period_inv_compat_all P j hlt hRoots
    exact ⟨hI.2.1, fun u hu => F_compatible_of_caches (hI.2.2.1 u hu)⟩
  · have hjc : x[j].time = supportCutoff S (s + 1) := le_antisymm hge hj
    -- `j` is at or before the step right after the hand-over update
    obtain ⟨-, -, hj₀t⟩ := stepBefore_spec x P.hDiv (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)
    have hjj₀ : j ≤ stepBefore x (supportCutoff S (s + 1) + 1) := by
      by_contra hc
      have := time_mono x (show stepBefore x (supportCutoff S (s + 1) + 1) + 1 ≤ j by omega)
      omega
    refine ⟨fun w hw _ => ?_, fun u hu => ?_⟩
    · have hkeep := (stateBefore_succ_keepsConfirmation x P.hDiv w hjc).2.2.2
      have hrec := (P.hHand.2.1 w hw).2.1
      rw [hrec] at hkeep
      rw [← hkeep]
      exact ⟨ancestorEq_refl B, by rw [hkeep]; exact latest_confirmed_mem_T_of_exec x j w⟩
    · exact F_compatible_of_caches (P.hHand.2.2.1 j u hjc hu)

/-- **Lemma 105.** The proof; the audited statement is in
`Statements/Executions/AsyncResilienceStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `s`: the hand-over slot; `B`: its proposal; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `anchor`: the time from
  which committee sleepiness holds; `tAwakeEnd`: the time from which the confirmed tips are read
; `b₀`, `b₁`: the start and the end of the period; `t`: the time up to
  which the steps are read. -/
theorem confirmedPersists_throughPeriod_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (B : Block V)
    (H t₀ anchor tAwakeEnd b₀ b₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁)
    (hCatch : CatchUpOnWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁)
    (hSyncF : SynchronyFromWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁)
    (hCatchF : CatchUpOnWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s + 1))
    (hGST : GST ≤ voteTime S (s + 1))
    (hb₀ : supportCutoff S (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k))
    (hHold : HoldersOutweighWhereOwed S Sched s b₀ b₁)
    (ht₀ : t₀ ≤ supportCutoff S (s + 1))
    (hHand : HandoverFactsOfChainBlock S Sched x s B H t₀ tAwakeEnd)
    (hRoots : RootsNameBlocksUntil S Sched x t) :
    ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t ∧
      FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t := by
  have P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ :=
    ⟨hDiv, hMono, hSync, hCatch, hSyncF, hCatchF, hParent, hOwner, hU, hAdvQ, hSleepK, hAnchor,
      hGST, hb₀, hb, hb₁, hHold, ht₀, hHand⟩
  have key := fun j (hj1 : b₀ ≤ x[j].time) (hj2 : x[j].time ≤ t) =>
    period_facts_from_handover P j (le_trans hb₀ hj1) (hRoots.mono hj2)
  refine ⟨fun v T Pb hv hTE hT hP w j hw hupd hb₀j hjt => ?_,
    fun v T Pb hv hTE hT hP w j hw hb₀j hjt => ?_⟩
  · have hPB := hHand.2.2.2.2.2.2 v T Pb hv hTE hT hP
    obtain ⟨hrec, hheld⟩ := (key j hb₀j hjt).1 w hupd hw
    exact ancestorEq_trans hPB (preceq_confirmedOf_of_record_and_F _ B hrec hheld
      ((key j hb₀j hjt).2 w (hw _ le_rfl)))
  · have hPB := hHand.2.2.2.2.2.2 v T Pb hv hTE hT hP
    rcases (key j hb₀j hjt).2 w (hw _ le_rfl) with hFB | hBF
    · exact ancestorEq_compatible hPB hFB
    · exact Or.inl (ancestorEq_trans hPB hBF)

omit [RootOrder] in
/-- **`GST` is at most the vote time of slot `s + 1`** under the top statement's premises: `GST` at
most `tGAT`, the honest round opening slots from `tGAT + 4Δ · healFrontSlots S` to `tAwakeEnd`, and
the slot `s` starting after `tAwakeEnd`.

Why: `GST ≤ tGAT ≤` the start of the first opening's slot `≤` the support cutoff of the last
opening's slot `≤ tAwakeEnd < slotStart S s < voteTime S (s + 1)`.

Promoted from `scratch/goldilocks_async/probe_ar4_replan.lean:127`, statement and proof unchanged.

The variables:
- `S`, `Sched`: the setup, the schedule; `GST`: the time from which the network is synchronous;
  `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the index of the last honest round opening slot;
  `s`: the hand-over slot; `r`: the rounds of the honest round opening slots.

Read aloud: the network is synchronous by the first votes after the hand-over proposal. -/
theorem gst_le_voteTime_succ_of_top (S : Setup V) (Sched : Schedule V)
    (GST tGAT tAwakeEnd m s : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : tAwakeEnd < slotStart S s) :
    GST ≤ voteTime S (s + 1) := by
  have hΔ := one_le_Δ S
  have h0m : r 0 ≤ r m := by
    have key : ∀ i, i ≤ m → r 0 ≤ r i := by
      intro i hi
      induction i with
      | zero => exact le_rfl
      | succ n ih =>
        exact le_trans (ih (Nat.le_of_succ_le hi)) (le_of_lt (hSeq.mono n (by omega)))
    exact key m le_rfl
  have h1 := hSeq.first
  have h2 := hSeq.last
  have h3 := slotStart_mono S (Nat.mul_le_mul_right S.C.R h0m)
  have h4 := supportCutoff_eq S (r m * S.C.R)
  have h5 := voteTime_eq S (r m * S.C.R)
  have h6 := voteTime_eq S (s + 1)
  have h7 := slotStart_mono S (show s ≤ s + 1 by omega)
  have h8 : tGAT ≤ tGAT + 4 * Δ S * healFrontSlots S := Nat.le_add_right _ _
  omega

/-- **The asynchrony top statement.** The proof; the audited statement is in
`Statements/Executions/AsyncResilienceStatements.lean`.

Route: when `t < b₀` no step is read. Otherwise roots name blocks up to `t` or a collision hit by
`t` (`rootsNameBlocksUntil_or_collision`); the facts after the hand-over up to the hand-over update
`c := supportCutoff S (s + 1)` (`healed_handover_facts_until_upTo` at `b := c`, `t := c`, the
delivery premises up to `b₀ ≥ c` from the suspended ones); the chain invariant and the lock
invariant at the slots after `s₀` and at most `s` (`lem81_inv_before_upTo` at `n := s + 1`); the
lock invariant at `s₀` (`base_locks_on_chain`); the voter condition at slot `s + 1`
; the records on the honest chain
(`lem90a_latest_confirmed_honest_at`); Lemma 99's two theorems
(`handoverFacts_six_of_healed_upTo`, `confirmed_tips_preceq_handover_upTo`, the latter read from
`tAwakeEnd ≥ x[i₂].time` on), which give `HandoverFactsOfChainBlock` with the lower end
`tAwakeEnd`; and Lemma 105 with `anchor := anchorCW S tGAT` and `GST ≤ voteTime S (s + 1)`
(`gst_le_voteTime_succ_of_top`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `tGAT`, `tAwakeEnd`: the start and end of the healing
  phase; `m`: the index of the last honest round opening slot; `r`: the rounds of the honest round opening slots; `s`: the hand-over
  slot; `b₀`, `b₁`: the start and the end of the period. -/
theorem confirmedPersists_asyncPeriod_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ) (s b₀ b₁ : ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁)
    (hCatch : CatchUpOnWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁)
    (hSyncF : SynchronyFromWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁)
    (hCatchF : CatchUpOnWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : tAwakeEnd < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hb₀ : supportCutoff S (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k))
    (hHold : HoldersOutweighWhereOwed S Sched s b₀ b₁) :
    ∀ t : ℕ,
      RootCollisionAtOpening S Sched x r m ∨ RootCollisionHeldBy S Sched x t ∨
        ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent →
          RootCollisionAtProposal S Sched x s B ∨
            (ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t ∧
              FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t) := by
  intro t
  rcases Nat.lt_or_ge t b₀ with htb | htb
  · -- no step at a time from `b₀` to `t`
    refine Or.inr (Or.inr fun i B _ _ => Or.inr ⟨?_, ?_⟩)
    · intro v T P _ _ _ _ w j _ _ hj1 hj2
      exact absurd (lt_of_le_of_lt (le_trans hj1 hj2) htb) (lt_irrefl b₀)
    · intro v T P _ _ _ _ w j _ hj1 hj2
      exact absurd (lt_of_le_of_lt (le_trans hj1 hj2) htb) (lt_irrefl b₀)
  rcases Proofs.Executions.rootsNameBlocksUntil_or_collision x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  have hOwner : VotesCastByOwner S Sched x :=
    Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono
  have hΔ := one_le_Δ S
  obtain ⟨hvS, hcS, hfS, hsS, -⟩ := times_eq S s
  obtain ⟨hvS1, hcS1, -, -, -⟩ := times_eq S (s + 1)
  -- the times: `tAwakeEnd < slotStart S s < c := supportCutoff S (s + 1) ≤ b₀ ≤ t`
  have hTc : tAwakeEnd ≤ supportCutoff S (s + 1) := by omega
  have hct : supportCutoff S (s + 1) ≤ t := le_trans hb₀ htb
  have hRootsC := hRootsT.mono hct
  -- the delivery premises up to `b₀`, from the suspended ones
  have hSync₀ := Proofs.Executions.synchronyFromWakeUpTo_of_outside hSync
  have hCatch₀ := Proofs.Executions.catchUpOnWakeUpTo_of_outside hCatch
  have hSyncF₀ := Proofs.Executions.synchronyFromWakeUpTo_of_outside hSyncF
  have hCatchF₀ := Proofs.Executions.catchUpOnWakeUpTo_of_outside hCatchF
  have hlast : slotStart S (r m * S.C.R) ≤ b₀ := by
    have h1 := hSeq.last
    have h2 := supportCutoff_eq S (r m * S.C.R)
    have h3 := voteTime_eq S (r m * S.C.R)
    omega
  -- the facts after the hand-over, up to the hand-over update
  rcases Proofs.Executions.healed_handover_facts_until_upTo S Sched x GST tGAT tAwakeEnd m r hGST
      hDiv hMono (hSync₀.mono hb₀) (hCatch₀.mono hb₀) (hSyncF₀.mono hlast) (hCatchF₀.mono hlast)
      hParent hU hThird hAwake hCommittees hSeq hOpenings hAdvQ (supportCutoff S (s + 1)) hTc
      le_rfl with
    hCol | hCol | ⟨s₀, i₂, B₀, hsc, hx2, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
      hCaches, hVF, hUF, hChain⟩
  · exact Or.inl hCol
  · obtain ⟨B₁, B₂, h1, h2, h3, hne⟩ := hCol
    exact absurd (hRootsC B₁ B₂ h1 h2 h3) hne
  right; right
  intro i B hlbl hsent
  by_cases hCol : RootCollisionAtProposal S Sched x s B
  · exact Or.inl hCol
  right
  -- the slots and the anchor
  have hs₀s : s₀ + 2 ≤ s := (slot_le_of_supportCutoff_lt S s₀ s).1 (by omega)
  have hAncS : anchorCW S tGAT ≤ slotStart S (s + 1) :=
    le_trans hAnc (slotStart_mono S (by omega))
  have hAnc₂ : anchorCW S tGAT ≤ x[i₂].time := by
    have h1 : slotStart S (s₀ + 1) ≤ supportCutoff S (s₀ + 1) := by
      rw [supportCutoff_eq, voteTime_eq]
      omega
    omega
  have hcsc : supportCutoff S s ≤ supportCutoff S (s + 1) := supportCutoff_mono S (Nat.le_succ s)
  have hSyncS := hSync₀.mono (le_trans hcsc hb₀)
  have hCatchS := hCatch₀.mono (le_trans hcsc hb₀)
  have hRootsH := hRootsC
  -- the chain before `s + 1`, and before `s − 1`
  have hChainS1 : ConfirmationsChainBefore S Sched x s₀ (s + 1) := hChain s le_rfl
  have hChainSm : ConfirmationsChainBefore S Sched x s₀ (s - 1) := by
    intro a b v v' C C' h1 h2 h3
    exact hChainS1 a b v v' C C' h1 h2 (by omega)
  -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
  have hcs1 : supportCutoff S (s + 1 - 1) ≤ b₀ := by
    rw [Nat.add_sub_cancel]
    exact le_trans hcsc hb₀
  have hInvAll := Proofs.Executions.lem81_inv_before_upTo S Sched x GST s₀ (anchorCW S tGAT)
    (s + 1) B₀ hDiv hMono (hSync₀.mono hcs1) (hCatch₀.mono hcs1)
    (hRootsT.mono (le_trans hcs1 htb)) hParent hOwner hGST' hCommittees hAnc hB₀slot hBase
    hBaseSaved
    (fun s' h₁ h₂ => hVF s' h₁ (supportCutoff_mono S (by omega)))
    (fun s' h₁ h₂ => hUF s' h₁ (supportCutoff_mono S (by omega)))
  have hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s' :=
    fun s' h₁ h₂ => (hInvAll s' h₁ (by omega)).1
  have hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' u :=
    fun s' h₁ h₂ => (hInvAll s' h₁ (by omega)).2
  have hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u :=
    fun u hu => Proofs.Executions.base_locks_on_chain S Sched x s₀ (anchorCW S tGAT) B₀ u hDiv
      hMono hCommittees hAnc hB₀slot hBase hBaseSaved hu
  -- the voter condition at slot `s + 1`
  have hvc : voteTime S (s + 1) ≤ supportCutoff S (s + 1) := by omega
  have hFrames : ∀ w ∈ honestActiveAt S Sched (s + 1), VoterFrameOnChainAt S Sched x s₀ (s + 1) w :=
    fun w hw => Proofs.Executions.voterFrame_after_handover_until_upTo S Sched x GST s₀ i₂
      (chainStateOf S.C B₀).h (s + 1) w hDiv hMono (hSync₀.mono (le_trans hvc hb₀))
      (hCatch₀.mono (le_trans hvc hb₀)) (hRootsC.mono hvc) hParent hU hAdvQ hGST' hOld
      (fun j u h₁ h₂ hu => hCaches j u h₁ (le_trans h₂ hvc) hu)
      (by rw [Nat.add_sub_cancel]; omega) hChainS1 hw
  -- the records, on the chain at a slot whose update ran by then
  have hLatest0 := Proofs.Executions.lem90a_latest_confirmed_honest_at S Sched x s₀ B₀ hDiv hMono
    hB₀slot hBase hBaseSaved hUpd
  have hLatest : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T := by
    intro j u h _ hu
    obtain ⟨⟨σ, hσ₀, hσ, w, hw, hsw⟩, hT⟩ := hLatest0 j u (lt_of_lt_of_le hsc h) hu
    exact ⟨⟨σ, hσ, hσ₀, w, hw, _, hsw, ancestorEq_refl _⟩, hT⟩
  -- Lemma 99: the hand-over facts, the confirmed tips read from `tAwakeEnd` on
  have hSix := Proofs.Executions.handoverFacts_six_of_healed_upTo S Sched x GST s₀
    (anchorCW S tGAT) i₂ (chainStateOf S.C B₀).h s B hDiv hMono hSyncS hCatchS hRootsH hParent
    hOwner hU hAdvQ hCommittees hAnc₂ hGST' hsc.le hChainSm hInv hLocks hLocks₀ hOld hCaches
    hFrames (by omega) hp ⟨i, hlbl, hsent⟩ hCol
  have hTips := Proofs.Executions.confirmed_tips_preceq_handover_upTo S Sched x GST s₀
    (anchorCW S tGAT) i₂ (chainStateOf S.C B₀).h s B hDiv hMono hSyncS hCatchS hRootsH hParent
    hOwner hU hAdvQ hCommittees hAnc₂ hGST' hsc.le hChainSm hInv hLocks hLocks₀ hOld hCaches
    hLatest (by omega) hp ⟨i, hlbl, hsent⟩ hCol
  have hHand : HandoverFactsOfChainBlock S Sched x s B (chainStateOf S.C B₀).h
      (supportCutoff S (s₀ + 1)) tAwakeEnd := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hSix
    unfold HandoverFactsOfChainBlock
    exact ⟨h1, h2, h3, h4, h5, h6,
      fun v T P hv hTE hT hP => hTips v T P hv (le_trans hx2 hTE) hT hP⟩
  -- Lemma 105
  exact Proofs.Executions.confirmedPersists_throughPeriod_until S Sched x GST s B
    (chainStateOf S.C B₀).h (supportCutoff S (s₀ + 1)) (anchorCW S tGAT) tAwakeEnd b₀ b₁ t hDiv
    hMono hSync hCatch hSyncF hCatchF hParent hOwner hU hAdvQ hCommittees hAncS
    (gst_le_voteTime_succ_of_top S Sched GST tGAT tAwakeEnd m s r hGST hSeq hs) hb₀ hb hb₁ hHold
    (supportCutoff_mono S (by omega)) hHand hRootsT

/-- **The asynchrony top statement, read forever.** The proof; the audited statement is in
`Statements/Executions/AsyncResilienceStatements.lean`.

Route: when the root collision at an honest round opening slot or a root collision among held blocks at some
time `t` occurred, the first two disjuncts. Otherwise, for a proposal `B` of the hand-over slot
with no root collision at its proposal, `confirmedPersists_asyncPeriod_until` at every time `t`
leaves only its last disjunct, so `ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t` and
`FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t` hold at every `t`, which are the unbounded
forms (`confirmedPersistsFrom_iff`, `finalizedCompatibleFrom_iff`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `tGAT`, `tAwakeEnd`: the start and end of the healing
  phase; `m`: the index of the last honest round opening slot; `r`: the rounds of the honest round opening slots; `s`: the hand-over
  slot; `b₀`, `b₁`: the start and the end of the period. -/
theorem confirmedPersists_asyncPeriod (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ) (s b₀ b₁ : ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁)
    (hCatch : CatchUpOnWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁)
    (hSyncF : SynchronyFromWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁)
    (hCatchF : CatchUpOnWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : tAwakeEnd < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hb₀ : supportCutoff S (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k))
    (hHold : HoldersOutweighWhereOwed S Sched s b₀ b₁) :
    RootCollisionAtOpening S Sched x r m ∨ (∃ t : ℕ, RootCollisionHeldBy S Sched x t) ∨
      ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
        (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent →
        RootCollisionAtProposal S Sched x s B ∨
          (ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀ ∧
            FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀) := by
  have h := Proofs.Executions.confirmedPersists_asyncPeriod_until S Sched x GST tGAT tAwakeEnd m r
    s b₀ b₁ hGST hDiv hMono hSync hCatch hSyncF hCatchF hParent hU hThird hAwake hCommittees hSeq
    hOpenings hAdvQ hs hp hb₀ hb hb₁ hHold
  by_cases hO : RootCollisionAtOpening S Sched x r m
  · exact Or.inl hO
  by_cases hH : ∃ t : ℕ, RootCollisionHeldBy S Sched x t
  · exact Or.inr (Or.inl hH)
  refine Or.inr (Or.inr fun i B hl hsent => ?_)
  by_cases hP : RootCollisionAtProposal S Sched x s B
  · exact Or.inl hP
  have hall : ∀ t : ℕ, ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t ∧
      FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t := by
    intro t
    rcases h t with h1 | h1 | h1
    · exact absurd h1 hO
    · exact absurd ⟨t, h1⟩ hH
    · rcases h1 i B hl hsent with h2 | h2
      · exact absurd h2 hP
      · exact h2
  exact Or.inr ⟨(confirmedPersistsFrom_iff S Sched x s tAwakeEnd b₀).2 fun t => (hall t).1,
    (finalizedCompatibleFrom_iff S Sched x s tAwakeEnd b₀).2 fun t => (hall t).2⟩

/-- A later lower end reads fewer steps: `ConfirmedPersistsBetween` from `b₀` gives it from any
`b₀' ≥ b₀`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are read; `b₀`, `b₀'`: the two lower ends;
  `t`: the time up to which the steps are read;
- `hb`: `b₀ ≤ b₀'`; `h`: the conclusion from `b₀`.

Read aloud: what persists at every step from `b₀` to `t` persists at every step from `b₀'` to `t`. -/
theorem confirmedPersistsBetween_mono_lower (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s tAwakeEnd b₀ b₀' t : ℕ) (hb : b₀ ≤ b₀')
    (h : ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t) :
    ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀' t :=
  fun v T P hT h1 h2 hP w j hj hw h3 h4 => h v T P hT h1 h2 hP w j hj hw (le_trans hb h3) h4

end GoldilocksCorrectness.Proofs.Executions
