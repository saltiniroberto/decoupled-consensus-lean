module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalViabilityStatements
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Statements.Executions.ProposalViabilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# RoundBase, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/RoundBase.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the base of the round, the slot invariant
restricted to the honest proposal, at its slot. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq supportCutoff_eq viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  FrameShape)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

open Classical in
/-- **Kit theorem, the base of the round, with the frames read at three points.** Write `s` for
the first slot of the round (`1 ≤ s`), `a` for the support cutoff of slot `s + 1`. In an execution
with the eight execution assumptions: if `GST` is at most the vote time of slot `s − 1`; the members
of `Hon` are awake and honest from the duty window's start of slot `s` to `a`; `p` is awake and
honest from the vote time of slot `s − 1` to the start of slot `s` and put `B` on the wire at its
tick then; the slot `s − 1` is as Lemma 59 reads it; every member of `Hs` is a member of `Hon` and
of the slot-`s` committee that put a slot-`s` vote on the wire; at every member the slot-`s` voters
of its pool before `a` are fewer than twice `Hs`; the slot-`s` committee is at most twice `Hs`;
`p`'s frame before the start of slot `s` has the root `ρp` and the `head_height_floor` `φ`; each
member `w`'s frame before the vote time of slot `s` has the root `ρw w`, on `B`'s parent's chain,
and the `head_height_floor` `φw w`, at least `φ` and at most the height of `B`'s parent; each
member's finalized block before `a` is `B` or an ancestor of `B`; and some block of
`p`'s tree on `X`'s and `ρp`'s chains reaches `φ` — then every member holds `B` before the vote
time of slot `s`, `HonestChainExtends M S Sched x Hon B s` holds, and every outcome `(n', sent)` of
a member's tick at `a`, from its state awake for slot `s + 1`, saves `B` as the confirmation of
slot `s` and has `B` among its fast blocks.

The landed statement reads each member's revocation of slot `s` and update of slot `s + 1` through
their answers; the twin reads the outcomes of the member's tick at the vote time of slot `s`
(template A1, on `hLocksW`) and at `a` (template A3, on the third conclusion), each from a state
awake for the slot. Every outcome at `a` saves and makes fast what the step's own outcome does:
the update's walk ends at one block (`confirmationUpdated_saved_eq`).

Why: the steps of the module header.

The proposer is read up to its own tick to the start of slot `s` from `tStart`, a clock value more than both clock
bounds before Lemma 12's read time of slot `s − 1`; each member is read up to its own tick to
the vote time of slot `s` from the same `tStart` (`hwR`, Lemma 59le's row `hw`); a real-time window of the members
gives that reader only when the slot arithmetic leaves room for one more `ΔClockAhead` (F-RC58-1).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s`: the first slot of the round;
- `Hon`: the members; `Hs`: the honest voters of slot `s`; `Hprev`: those of slot `s − 1`, with `H`
  the block each one's vote is for; `X`: the block they extend; `B`: the proposal; `p`: its
  proposer;
- `φ`, `ρp`: the `head_height_floor` and the root of `p`'s frame before the start of slot `s`;
  `φw w`, `ρw w`: those of member `w`'s frame before the vote time of slot `s`.

Read aloud: in the round's first slot every member votes for the honest proposal, confirms it,
makes it fast and keeps no lock off its chain.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 42, which the proof calls at slot `s`
for each member's revocation of slot `s + 1`, takes blocks as held up to the support cutoff of
slot `s + 1`; Lemmas 22, 27, 59 and 60 read earlier. -/
theorem round_base_steps (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hon Hs Hprev : Finset V) (H : V → Block V) (X B : Block V) (p : V) (φ : Height)
    (φw : V → Height) (ρp : Block V) (ρw : V → Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hs1 : 1 ≤ s)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the members each run the update of slot `s`, and none is in the adversary set at a step where a validator outside
    -- it ticks to the support cutoff of slot `s + 1` (Lemma 80's rows for slot `s`,; the
    -- real-time window `hHon` is dropped, re-check 60 section 1.5)
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- each member ticks to the vote time of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart` (Lemma 59le's row `hw`, F-RC58-1, F-RC58-4)
    (hwR : ∀ w ∈ Hon, w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hHsPrev : ∀ u ∈ Hprev, u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hprev, u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * Hprev.card)
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C s))
      ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
        2 * Hs.card)
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) ρp φ)
    (hShapeW : ∀ w ∈ Hon, FrameShape M (x.tickInput w (M.voteTime S.C s)) (ρw w) (φw w))
    (hFloorW : ∀ w ∈ Hon, φ ≤ φw w ∧ φw w ≤ (M.chainStateOf S.C B.parent).h)
    (hRootW : ∀ w ∈ Hon, (ρw w).AncestorEq B.parent)
    -- each member's finalized block at its tick to the support cutoff of slot `s + 1` is `B` or an ancestor of `B`
    -- (: the finalized block in place of the fork-choice root)
    (hFinAr : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h) :
    (∀ u ∈ Hon, B ∈ (x.tickInput u (M.voteTime S.C s)).tree) ∧
    HonestChainExtends M S A x Hon B s ∧
    ∀ v ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) →
      M.savedConfirmation n' s = some B ∧ B ∈ M.fastBlocks n' := by
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hGST hHsPrev htStart hHold
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  obtain ⟨hvA, hcA, hfA, hsA, -, hk8, hΔ⟩ := (slot_times M F U) S s₀
  obtain ⟨hvB, hcB, hfB, hsB, -, -, -⟩ := (slot_times M F U) S (s₀ + 1)
  obtain ⟨hvC, hcC, -, -, hdC, -, -⟩ := (slot_times M F U) S (s₀ + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s₀
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hdw2 := duty_window_start_real S (s₀ + 1 + 1)
  push_cast at hdw2
  have hsBR : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 4 * Δ S := by
    rw [hsA, hss]; push_cast; ring
  have hvBR : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 5 * Δ S := by
    rw [hvB, hsA, hss]; push_cast; ring
  have hcBR : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 6 * Δ S := by
    rw [hcB, hsA, hss]; push_cast; ring
  have hfBR : ((M.viewFreeze S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 7 * Δ S := by
    rw [hfB, hsA, hss]; push_cast; ring
  have hvCR : ((M.voteTime S.C (s₀ + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 9 * Δ S := by
    rw [hvC, hsB, hsA, hss]; push_cast; ring
  have hcCR : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 10 * Δ S := by
    rw [hcC, hsB, hsA, hss]; push_cast; ring
  have hcc : M.supportCutoff S.C s₀ ≤ M.supportCutoff S.C (s₀ + 1) := by omega
  have hGST₁ : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s₀ + 1) := le_trans hGST hcc
  -- the members' readers: of slot `s₀ + 1`'s update (`hU`), and the ticks inside it
  have hU : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₀ + 1 + 1))
      (M.supportCutoff S.C (s₀ + 1 + 1)) := fun v hv => hHonUpd v hv
  have hUc : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₀ + 1 + 1))
      (M.supportCutoff S.C (s₀ + 1)) := fun v hv =>
    (mem_activeThroughoutToTick_of_inside M F) R E (hU v hv) (by omega)
      (by rw [hdw2, hcBR]; linarith) (by rw [hcBR, hcCR]; linarith)
  have hUf : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₀ + 1 + 1))
      (M.viewFreeze S.C (s₀ + 1)) := fun v hv =>
    (mem_activeThroughoutToTick_of_inside M F) R E (hU v hv) (by omega)
      (by rw [hdw2, hfBR]; linarith) (by rw [hfBR, hcCR]; linarith)
  have hUv : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s₀ + 1 + 2) : ℕ) : ℤ)
      (M.voteTime S.C (s₀ + 1 + 1)) := fun v hv =>
    (vote_reader_from_updater_under_skew M F U) S A x R (s₀ + 1) v E hSkew (hHonUpd v hv)
  -- the roots at a member's own ticks
  have hRootsAt : ∀ (c₀ : ℕ), c₀ ≤ M.supportCutoff S.C (s₀ + 1 + 1) → ∀ (k : ℕ) (v : V),
      x.lbl k = Event.tick v c₀ → RootsNameBlocksUntil M A x (x.time (x.tickStep v c₀)) :=
    fun c₀ hc₀ k v hk => (roots_at_own_tick_of_per_tick M F) x E
      (fun k u c hk hc => hRoots k u c hk (le_trans hc hc₀)) hk
  -- step 1: `p` holds `B` after its tick, and every member holds `B` at its tick to the vote time of slot `s`
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨-, hBne, hBpar?, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s₀ i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentHeld : B.parent ∈ (x.tickInput p (M.slotStart S.C (s₀ + 1))).tree := by
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).1
    · obtain ⟨W, hW, hXW, -, -⟩ := hHeadP
      refine (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
        (x.tickStep p (M.slotStart S.C (s₀ + 1))) p W B.parent hW ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (x.tickInput p (M.slotStart S.C (s₀ + 1))).finalized.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F)
          S A x R E (x.tickStep p (M.slotStart S.C (s₀ + 1))) p)
        (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
            exact (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _)
  have hBp : B ∈ (x.st (i + 1) p).tree :=
    (lem22a_proposer_holds_own_proposal M F U) S A x R s₀ i B p E hl hsent hRootNew hParentHeld
      ((compatible_iff _ _).2 (Or.inl hFpB))
  have hvsB : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by
    rw [hsBR, hvBR]; linarith
  have hcut0 : (((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ)) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C s₀ - max (2 * Δ S) Δs ≤ M.slotStart S.C (s₀ + 1) by omega)
  have hHeld : ∀ u ∈ Hon, B ∈ (x.tickInput u (M.voteTime S.C (s₀ + 1))).tree := by
    intro u hu
    obtain ⟨kU, hkU, -⟩ := Activity.mem_activeThroughoutToTick.1 (hwR u hu)
    have hFu : (x.tickInput u (M.voteTime S.C (s₀ + 1))).finalized.AncestorEq B := by
      refine ancestorEq_trans ?_ (ancestorEq_trans (hRootW u hu) hPB)
      rw [← (hShapeW u hu).1]
      exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ u
    exact (lem22_proposal_held_by_voter M F U) S A x R GST s₀ i B p u E hNet hSkew hRedeliver
      (hRootsAt _ (by omega) kU u hkU) hParent (by omega)
      ((tick_window_of_activeThroughoutToTick_int M) x R E (hwR u hu) (by push_cast; linarith))
      hl hsent hBp ((compatible_iff _ _).2 (Or.inl hFu))
  -- step 2: every member's slot-`s` vote is its vote for `B` (Lemma 59le)
  have hVote : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₀ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      vote = GoldfishVote.mk u (s₀ + 1) B.root := by
    intro u hu vote hSend
    obtain ⟨kU, hkU, -⟩ := Activity.mem_activeThroughoutToTick.1 (hwR u hu)
    have hhead := (lem59le_goldfish_vote_names_honest_proposal_frame M F U) S A x R GST s₀ Hprev H X B
      p u vote ρp (ρw u) φ (φw u) E hNet hSkew hRedeliver Sy hΔs (hRootsAt _ (by omega) kU u hkU) hParent
      hOwner hGST
      (fun u' hu' => ⟨(hHsPrev u' hu').1, (hHsPrev u' hu').2.1 u hu, (hHsPrev u' hu').2.2⟩)
      (hVotersPrev u hu) hHold tStart htStart hp hHoldP (hwR u hu) hPropose hSend
      (hOnly u hu) hRootNew hShapeP (hShapeW u hu) (hFloorW u hu).1 hHeadP hApX
      (ancestorEq_trans (hRootW u hu) hPB)
      (fun n' sent hrun hA e he hlive => ancestorEq_trans (hLocksW u hu n' sent hrun hA e he hlive) hPB)
      (hFloorW u hu).2
    obtain ⟨hvi, hvs⟩ := (honest_vote_form M F U) S A x R E (s₀ + 1) u vote hSend
    cases vote with
    | mk vi vs vh =>
        simp only at hvi hvs hhead
        rw [hvi, hvs, hhead]
  -- the honest voters of slot `s` as Lemmas 60 and 27 read them at member `v`'s tick to the support cutoff
  -- of slot `s + 1`
  have hHs' : ∀ v ∈ Hon, ∀ u ∈ Hs, u ∈ S.P.committee (s₀ + 1) ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s₀ + 1 + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₀ + 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₀ + 1) B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C (s₀ + 1))).tree := by
    intro v hv u hu
    obtain ⟨huH, hcomm, vote, -, -, i', hl', hs'⟩ := hHs u hu
    have hvt := hVote u huH vote ⟨i', hl', hs'⟩
    rw [hvt] at hs'
    exact ⟨hcomm, (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E (hU v hv) (hHonTick u huH),
      ⟨i', hl', hs'⟩, hHeld u huH⟩
  have hHoldHs : ∀ u ∈ Hs, u ∈ A.activeThroughout x
      ((M.supportCutoff S.C (s₀ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₀ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun u hu =>
    (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST₁ (hU u (hHs u hu).1)
  have hRootsC : ∀ v ∈ Hon, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1)))) := by
    intro v hv
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hUc v hv)
    exact hRootsAt _ (by omega) k v hk
  -- the finalized block of a member at its tick to the support cutoff of slot `s + 1` is `B` or an ancestor of `B`
  have hFa : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1))).finalized.AncestorEq B := by
    exact hFinAr
  -- step 3: every member's update makes `B` fast (Lemma 60), the update an outcome of its tick runs
  have hUpd : ∀ v ∈ Hon, ∃ n'' : M.N,
      ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1)))
        ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : Int) (s₀ + 1 + 1) n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1 + 1))).savedConfirmation =
        M.savedConfirmation n'' ∧ B ∈ M.fastBlocks n'' := by
    intro v hv
    have hfast := ((GoldilocksCorrectness.Record.Proofs.Executions.lem29_update_confirmation_fast_locks_voter_majority_block M F U) S A x R GST (s₀ + 1) Hs B v E hNet hSkew
      hRedeliver Sy hΔs (hRootsC v hv) hParent hOwner hGST₁ (hHs' v hv) hHoldHs (hVoters v hv) hHalf hBne
      (hU v hv) (hFa v hv)).1
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 (hU v hv)
    obtain ⟨n'', sent, hrun, hAwake, hsave, hfb, -, -⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.update_state_of_duty M F U) S A x R (s₀ + 1) v E hk'
        ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E (hU v hv)
          ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
            F.sched U) S (s₀ + 1 + 1)))
    exact ⟨n'', (confirmationUpdated_of_cutoff_tickInput M F U) x R (s₀ + 1) v n'' sent hrun hAwake, hsave,
      by rw [← hfb]; exact hfast⟩
  -- Lemma 42's windows, from the members' readers
  have hdwC : M.dutyWindowStart S.C (s₀ + 1 + 1) + Δ S ≤
      M.supportCutoff S.C (s₀ + 1 + 1) - max (6 * Δ S) Δs ∧
      M.dutyWindowStart S.C (s₀ + 1 + 1) + Δ S ≤ M.viewFreeze S.C (s₀ + 1) - max (3 * Δ S) Δs := by
    clear * - hdC hkm hGST hcA hsA hsB hcC hfB hk8
    refine ⟨?_, ?_⟩ <;> omega
  have htStartV : ((M.dutyWindowStart S.C (s₀ + 1 + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s₀ + 1 + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by
    have hR : ((M.dutyWindowStart S.C (s₀ + 1 + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (s₀ + 1 + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hdwC.1
    rw [Nat.cast_add] at hR
    linarith
  have htStartW : ((M.dutyWindowStart S.C (s₀ + 1 + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C (s₀ + 1) - max (3 * Δ S) Δs : ℕ) : ℝ) := by
    have hR : ((M.dutyWindowStart S.C (s₀ + 1 + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.viewFreeze S.C (s₀ + 1) - max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hdwC.2
    rw [Nat.cast_add] at hR
    linarith
  have hdle := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
    M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  -- step 4: every lock entry a member's revocation of slot `s + 1` leaves is compatible with `B` (Lemma 42 with
  -- the member's own update making `B` fast)
  have hLocks : ∀ w ∈ Hon, ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s₀ + 1 + 1)))
        ((M.voteTime S.C (s₀ + 1 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s₀ + 1 + 1))) (s₀ + 1 + 1) →
      ∀ e ∈ M.lockEntries n'', e.B.compatible B = true := by
    intro w hw n'' sent hrun hAwake
    obtain ⟨nw, hUw, -, hfw⟩ := hUpd w hw
    obtain ⟨kV, hkV, -⟩ := Activity.mem_activeThroughoutToTick.1 (hUv w hw)
    obtain ⟨kC, hkC, -⟩ := Activity.mem_activeThroughoutToTick.1 (hU w hw)
    have hkVC : kV ≤ kC := by
      have h1 := (E.time_tickStep ⟨kV, hkV⟩).2
      have h2 := (E.time_tickStep ⟨kC, hkC⟩).1
      rw [(tickStep_eq_of_lbl M) x E hkV] at h1
      rw [(tickStep_eq_of_lbl M) x E hkC] at h2
      by_contra hc
      have := R.time_mono (Nat.le_of_not_le hc)
      rw [hvCR] at h1
      rw [hcCR] at h2
      linarith
    have hF : (x.tickInput w (M.voteTime S.C (s₀ + 1 + 1))).finalized.compatible B = true := by
      have hin : x.tickInput w (M.voteTime S.C (s₀ + 1 + 1)) = x.st kV w := by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
      have hc : x.tickInput w (M.supportCutoff S.C (s₀ + 1 + 1)) = x.st kC w := by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkC]
      have hmono := (F_ancestorEq_of_le M F) x R E w hkVC
      rw [← hin, ← hc] at hmono
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hmono (hFa w hw)))
    have hR42 : RootsNameBlocksUntil M A x ((M.viewFreeze S.C (s₀ + 1) : ℝ) + ΔClockBehind) := by
      refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_
        (hRootsAt _ le_rfl kC w hkC)
      have h2 := (E.time_tickStep ⟨kC, hkC⟩).1
      rw [hcCR] at h2
      have : ((M.viewFreeze S.C (s₀ + 1) : ℕ) : ℝ) = 4 * Δ S * s₀ + 7 * Δ S := hfBR
      linarith
    -- `w` is active through the sync delay after the view freeze of slot `s` less one delay or one sync delay,
    -- a window inside its update reader (`mem_activeThroughout_of_mem_activeThroughoutToTick_real`,)
    have hV0w : w ∈ A.activeThroughout x ((M.viewFreeze S.C (s₀ + 1) - max (Δ S) Δs : ℕ) : ℝ)
        (((M.viewFreeze S.C (s₀ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
      have hmf : max (Δ S) Δs ≤ M.viewFreeze S.C (s₀ + 1) := by omega
      have hmR : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := Nat.cast_max _ _
      have hm1R : (Δ S : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_left _ _
      have hm2R : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
      rw [show (((M.viewFreeze S.C (s₀ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) =
        ((M.viewFreeze S.C (s₀ + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) by push_cast; ring]
      refine (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hU w hw) ?_ ?_
      · rw [Nat.cast_sub hmf, hfBR, hmR]
        linarith [hdw2]
      · rw [Nat.cast_add, Nat.cast_sub hmf, hfBR, hmR, hcCR]
        linarith
    have h42 := (lem42_fast_lock_clears_own_locks M F U) S A x R GST (s₀ + 1) B w nw E
      hNet hSkew hRedeliver Sy hΔs hR42 hParent (by omega) (M.dutyWindowStart S.C (s₀ + 1 + 1)) htStartV
      (Activity.mem_activeThroughoutToTick_of_le hdle (hU w hw)) (M.dutyWindowStart S.C (s₀ + 1 + 1)) htStartW
      (Activity.mem_activeThroughoutToTick_of_le hdle (hUf w hw)) hV0w hUw hfw kV hkV hF
    exact h42 n'' ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1 + 1) w n'' sent hrun hAwake)
  -- step 5: every member's update saves `B` as the confirmation of slot `s` (Lemma 27)
  have hSaved : ∀ v ∈ Hon,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1 + 1))).savedConfirmation (s₀ + 1) = some B := by
    intro v hv
    exact ((lem27_update_confirmation_confirms_voter_majority_block M F U) S A x R GST (s₀ + 1) Hs B v
      E hNet hSkew hRedeliver Sy hΔs (hRootsC v hv) hParent hOwner hGST₁ (hHs' v hv) hHoldHs
      (hVoters v hv) hBne (hU v hv) (hFa v hv)
      (fun n' sent hrun hA e he _ => hLocks v hv n' sent hrun hA e he)).1
  refine ⟨hHeld, ⟨fun u hu vote hSend => ⟨B, hHeld u hu, hVote u hu vote hSend, ancestorEq_refl B⟩,
    fun w hw n'' sent hrun hA e he _ => hLocks w hw n'' sent hrun hA e he, fun v hv C' hC' => ?_⟩,
    fun v hv n' sent hrun hAwake => ?_⟩
  · rw [hSaved v hv] at hC'
    cases hC'
    exact ancestorEq_refl B
  · -- every outcome of the tick at the support cutoff of slot `s + 1` saves and makes fast what the step's own
    -- outcome does: the update's walk ends at one block (`confirmationUpdated_saved_eq`), and the fast blocks are
    -- read off the saved confirmation when no live lock entry vetoes it
    obtain ⟨n'', hU'', hsave, hfb⟩ := hUpd v hv
    have hU' := (confirmationUpdated_of_cutoff_tickInput M F U) x R (s₀ + 1) v n' sent hrun hAwake
    have hs1' : 1 ≤ s₀ + 1 + 1 := by omega
    have hS'' : n''.savedConfirmation (s₀ + 1 + 1 - 1) = some B := by
      rw [Nat.add_sub_cancel]
      show M.savedConfirmation n'' (s₀ + 1) = some B
      rw [← hsave]
      exact hSaved v hv
    have hS' := (confirmationUpdated_saved_eq M F) hs1' hU'' hU' hS''
    rw [Nat.add_sub_cancel] at hS'
    obtain ⟨H', hH'', hveto, hBT, hBg, hBH, hft⟩ :=
      GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_fast_cases hs1' hU'' hfb
    have hH' := (confirmationUpdated_saved_eq M F) hs1' hU'' hU' hH''
    obtain ⟨-, -, -, hv0⟩ :=
      GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_saved_some hs1' hU' hH'
    exact ⟨hS', ((hv0 hveto).2.1 B).2 ⟨hBT, hBg, hBH, hft⟩⟩

end GoldilocksCorrectness.Record.Proofs.Executions

