module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBase
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalViability
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.RoundBase
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma80, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma80.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the kit of Lemma 80 (the parent of a viable
proposal, the members' window, Lemma 79's step over the members' sets, `HonestChainExtends` through
the round, the round's attestations in the pool, the later honest proposal extends the round's, the
conditions read from frame shapes), and Lemma 80, the height advances in a round. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq slotStart_le_of_le slot_add_two_le_of_delivery slot_eq_of_mem
  supportCutoff_eq supportCutoff_le_slotStart_succ viewFreeze_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

open GoldilocksCorrectness.Proofs.Routines (get_head_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes FrameShape
  ProposalCountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Kit fact, the parent of an honest proposal reaches its proposer's `head_height_floor`.**
When `p` put `B` on the wire at its tick at the start of slot `s + 1` and `B`'s parent is in the
viable tree of `p`'s frame before that start, the chain-state height of `B`'s parent is at least
the `head_height_floor` of `p`'s FG state then.

Why: `B`'s parent is the head of `p`'s fork choice (Lemma 19), a viable head (Lemma 58), whose
height is at least the `head_height_floor`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
  `B`: the proposal; `p`: its proposer.

Read aloud: the parent of an honest proposal has chain-state height at least its proposer's
`head_height_floor`. -/
theorem proposal_parent_viable (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      (M.chainStateOf S.C B.parent).h := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
  -- the slot of the slot's start, read by the spec's clock (the model's slot of a natural-number time is the
  -- spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
      (by omega)
  -- `p`'s run and proposal, at its tick `i` (Lemma 19 over the record, the field `tick_proposal` of `F.tk3`, from the
  -- tick's input state, which satisfies the node invariant: `p` is outside the adversary set at its tick)
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hti : x.tickInput p (M.slotStart S.C (s + 1)) = x.st i p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hpi : p ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i p hpi).1
  obtain ⟨-, -, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hInv hB₁
  rw [hslot₁, Nat.add_sub_cancel] at hWalkP
  rw [hslot₁] at hBdef
  -- `p`'s walk, `PoolHeadOf`'s
  obtain ⟨votes_p, support_p, -, hW⟩ := hWalkP
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  -- Lemma 58 over the record: the end of the walk, in the viable tree, is a viable head of `p`'s frame
  -- (`walk_end_viable_of_below`, the frame's tree holding every block between the fgroot and one of its blocks, by
  -- the node invariant and Lemma 46), all at the tick's step `i`
  rw [hBpar] at hParentIn
  obtain ⟨-, hρH, W, hW', hHW⟩ :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hParentIn
  have hClosed : ∀ Z' ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree, ∀ c : Block V,
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root.AncestorEq c → c.AncestorEq Z' →
        c ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree := by
    intro Z' hZ' c hρc hcZ
    rw [hti] at hZ' hρc ⊢
    refine (GoldilocksCorrectness.Record.Statements.Executions.frame_path_of_exec M F) S A x R E i p Z' c hZ' ?_ hcZ
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    refine ancestorEq_trans ((F_ancestorEq_fc_root_of_exec M F) S A x R E i p) ?_
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact hρc
  have hVH : Hp ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads := by
    by_cases hHWe : Hp = W
    · rw [hHWe]
      exact (Finset.mem_inter.1 hW').2
    · exact (GoldilocksCorrectness.Record.Proofs.Routines.walk_end_viable_of_below M F) S.C _ _ _ _ _ _
        s Hp W hClosed hW hρH (Finset.mem_inter.1 hW').1 (Finset.mem_inter.1 hW').2 hHW hHWe
  obtain ⟨-, -, -, hfl⟩ :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInv _).1 hVH
  rw [← hBpar] at hfl
  exact hfl

/-- **Kit fact, a member of a later slot's set is awake and honest from the round's start.** When
the member sets shrink from slot to slot and each member of the set of slot `s'` is awake and
honest from the duty window's start of slot `s'` to the support cutoff of slot `s' + 1` (and not
past the start of slot `s''`): every member of the set of slot `s + d` is awake and honest from the
duty window's start of slot `s` to the support cutoff of slot `s + d + 1`, not past the start of
slot `s''`.

Why: by induction on `d`; the windows of consecutive slots overlap, the duty window of slot
`s' + 1` starting before the support cutoff of slot `s' + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`: the setup, the schedule; `s`: the round's first slot; `s''`: the end of the window;
  `Hon`: the member sets.

Read aloud: a member of a later slot's set is awake and honest from the round's first duty window to
its own slot's support cutoff. -/
theorem members_window_of_sets (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s s'' : ℕ)
    (Hon : ℕ → Finset V)
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughout x (M.dutyWindowStart S.C s')
        (min (M.supportCutoff S.C (s' + 1)) (M.slotStart S.C s''))) :
    ∀ d : ℕ, s + d < s'' → ∀ v ∈ Hon (s + d),
      v ∈ A.activeThroughout x (M.dutyWindowStart S.C s)
        (min (M.supportCutoff S.C (s + d + 1)) (M.slotStart S.C s'')) := by
  intro d
  induction d with
  | zero =>
      intro hd v hv
      exact hHon s le_rfl (by omega) v hv
  | succ d ih =>
      intro hd v hv
      rw [show s + (d + 1) = s + d + 1 by omega] at hd hv ⊢
      have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S (s + d)
      have hΔ := one_le_Δ S
      have hss : M.slotStart S.C (s + d + 1) = M.slotStart S.C (s + d) + 4 * Δ S := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
      have hc : M.supportCutoff S.C (s + d + 1) = M.voteTime S.C (s + d + 1) + Δ S :=
        (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + d + 1)
      have hv1 : M.voteTime S.C (s + d + 1) = M.slotStart S.C (s + d + 1) + Δ S :=
        (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + d + 1)
      have hs'' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S
        (show s + d + 1 ≤ s'' by omega)
      -- the window of slot `s + d + 1` starts no later than the end of the window of slot `s + d`
      exact (mem_activeThroughout_union M) x R (ih (by omega) v (hHonMono (s + d) (by omega) (by omega) hv))
        (hHon (s + d + 1) (by omega) (by omega) v hv) (by first | (norm_cast; omega) | norm_cast)

open Classical in
/-- **Kit theorem, Lemma 79a over two sets.** As Lemma 79a, with the voters of slot `s'` in `Hon`
(where the invariant is read) and the votes of slot `s' + 1` read at the members of `Hon' ⊆ Hon`:
if `HonestChainExtends M S Sched x Hon B s'` holds, every member of `Hs` is a member of `Hon` voting
at slot `s'` and honest at the vote time of slot `s' + 1` and active through the sync delay after Lemma 12's read time at slot `s'`, and every member `w` of `Hon'` is awake
and honest from the duty window's start of slot `s' + 1` to its vote time, counts fewer than twice
`Hs`, has its fork-choice root compatible with `B` and, when that root is `B` or an ancestor of `B`,
a viable head of its voter tree on `B`'s chain — then every slot-`(s' + 1)` vote of a member of
`Hon'` is for a block it holds on `B`'s chain.

Why: Lemma 26b at each member of `Hon'`, the voters' blocks from the invariant's first clause and
the member's locks from its second clause.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s'`: the slot; `Hon`, `Hon'`: the two sets; `Hs`: the honest voters of slot
  `s'`; `B`: the block.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s'`: Lemma 26b, which
the proof calls at slot `s'`, reads them at each member's own tick to that cutoff.

Read aloud: when the honest chain extends `B` at slot `s'` for `Hon`, every slot-`(s' + 1)` vote of
a member of `Hon'` is for a block it holds on `B`'s chain. -/
theorem lem79a_votes_step_sets (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon Hon' Hs : Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s'`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hInv : HonestChainExtends M S A x Hon B s')
    (hSub : Hon' ⊆ Hon)
    -- no voter of `Hs` is in the adversary set at a step where a validator outside it ticks to the vote time of slot
    -- `s' + 1` (Lemma 26b reads the voters' honesty at the member's tick)
    (hHsHon : ∀ u ∈ Hs, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.voteTime S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- every member of `Hon'` ticks to the support cutoff of slot `s'` and is active at every step from Lemma 12's read
    -- time `supportCutoff s' − max (2 * Δ S) Δs` up to that tick (Lemma 12's receiver window, all the proof reads of
    -- the members' activity;)
    (hCore' : ∀ v ∈ Hon', ∃ kR : ℕ, x.lbl kR = Event.tick v (M.supportCutoff S.C s') ∧
      ∀ i : ℕ, ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kR → v ∈ A.active i)
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- every voter of `Hs` is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s' − max (2 * Δ S) Δs` (: Lemma 26b's holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersW : ∀ w ∈ Hon', ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1)))
        (s' + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hF2 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
        (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
          B.AncestorEq W) :
    ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro w hw vote hSend
  -- each voter of slot `s'` voted for a block it holds on `B`'s chain (clause 1 of the invariant at `Hon`)
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hInv.1 u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  -- Lemma 12's receiver window for `w` (the row `hCore'`;)
  obtain ⟨kR, hkR, -⟩ := hCore' w hw
  have hkRs : x.tickStep w (M.supportCutoff S.C s') = kR := (tickStep_eq_of_lbl M) x E hkR
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held M F U)
    S A x R GST s' Hs H' B w vote E hNet hSkew hRedeliver Sy hΔs (by rw [hkRs]; exact hRoots kR w _ hkR le_rfl)
    hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hSend.choose_spec.1 (hHsHon u hu),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) hHold (hCore' w hw) (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w (hSub hw)) hSend

open Classical in
/-- **Kit theorem, Lemma 79's step from one slot's set to the next.** As Lemma 79, with the voters
of slot `s'` in `Hon`, each running the update of slot `s'`, and the voters of slot `s' + 1` and the
members in `Hon' ⊆ Hon`, active from the duty window's start of slot `s' + 1` to its vote time, each
running the update of slot `s' + 1` and outside the adversary set at every honest validator's tick to the
support cutoff of slot `s' + 2`; the
counting and frame conditions are read at the members of `Hon'` — then
`HonestChainExtends M S Sched x Hon B s'` gives `HonestChainExtends M S Sched x Hon' B (s' + 1)`.

Why: `lem79a_votes_step_sets`; Lemma 79b at `Hon'` with the invariant restricted
(`honestChainExtends_mono`); Lemma 79c at `Hon'`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s'`: the slot; `Hon`, `Hon'`: the sets of slots `s'` and `s' + 1`; `Hs`: the
  honest voters of each slot; `B`: the block.

Read aloud: each slot's voters need to be honest only through their own slot's update.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 79c,
which the proof calls at slot `s'`, reads them there; `lem79a_votes_step_sets` reads them up to the support cutoff
of slot `s'`. -/
theorem lem79_step_sets (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon Hon' : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hInv : HonestChainExtends M S A x Hon B s')
    (hSub : Hon' ⊆ Hon)
    -- each member of `Hon` runs the update of slot `s'`
    (hHon : ∀ v ∈ Hon, v ∈ updaterAt M S A x s')
    -- the members of `Hon'` tick to the vote time of slot `s' + 1`, active up to that tick from the trace's start or
    -- from their own tick to a clock value at most the duty window's start of slot `s' + 1`, each runs
    -- the update of slot `s' + 1`, and none is in the adversary set at a step where a validator outside it ticks to the
    -- support cutoff of slot `s' + 2`
    (hHon' : ∀ v ∈ Hon', v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    (hHonUpd' : ∀ v ∈ Hon', v ∈ updaterAt M S A x (s' + 1))
    (hHonTick' : ∀ u ∈ Hon', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hHs' : ∀ u ∈ Hs (s' + 1), u ∈ Hon' ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersW : ∀ w ∈ Hon', ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1)))
        (s' + 1) votes support_votes →
      M.voters_count votes < 2 * (Hs s').card)
    (hVotersV : ∀ v ∈ Hon',
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    (hF2 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon',
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
        (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
          B.AncestorEq W)
    (hFv : ∀ v ∈ Hon',
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    HonestChainExtends M S A x Hon' B (s' + 1) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨hv2, hc2, -, hs2, -, -, -⟩ := (slot_times M F U) S (s' + 2)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hdw2 := duty_window_start_real S (s' + 2)
  push_cast at hdw2
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hcc : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) := by omega
  have hInv' := (honestChainExtends_mono M F) S A x Hon Hon' B s' hSub hInv
  -- clause 1 (`lem79a_votes_step_sets`): the voters of slot `s'`, updaters of slot `s'`, are honest at the vote time
  -- of slot `s' + 1`, before their ticks to the support cutoff of slot `s' + 1`
  have h1 := (lem79a_votes_step_sets M F U) S A x R GST s' Hon Hon' (Hs s') B E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hk hc => hRoots k u c hk (le_trans hc hcc)) hParent hOwner hGST hInv hSub
    (fun u hu => (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E (hHon u (hHs u hu).1)
      (by rw [hv1R, hc1R]; linarith))
    (fun v hv => (core_window_of_dutyWindow_reader M F U) x R E hΔs hSkew hGST (hHon' v hv)) hHs
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hHon u (hHs u hu).1))
    hVotersW hF2 hF3
  -- every member of `Hon'` ticks to the vote time of slot `s' + 1`, active up to that tick from its tick to a
  -- clock value at most the duty window's start of slot `s' + 2`: its reader of slot `s' + 1`
  have hwin : ∀ w ∈ Hon', w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)) :=
    fun w hw => (reader_from_updater_under_skew M F U) S A x R s' w E hSkew (hHonUpd' w hw)
  refine ⟨h1, ?_, ?_⟩
  · -- clause 2 (Lemma 79b at `Hon'`), on the revocation the outcome of a member's tick to the vote time of slot
    -- `s' + 2` ran from its tick input (the field `tick_voteTime_locks_of_core` of `F.tk2`)
    intro w hw n' sent hrun hAwake e he hlive
    have hsl : S.C.slot ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) = s' + 1 + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
        (by rw [show s' + 1 + 1 = s' + 2 by omega]; omega) (by rw [show s' + 1 + 1 = s' + 2 by omega]; omega)
    have hInvW := (lem11_node_invariantCore_of_run M F S x R (x.tickStep w (M.voteTime S.C (s' + 1 + 1))) w).1
    have hRevoke := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n' sent hrun hInvW
      (by
        rw [hsl]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s' + 1 + 1))
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hRevoke
    exact (lem79b_honestChainExtends_locks_step M F U) S A x R s' Hon' B E hInv' hwin w hw n' hRevoke e he hlive
  · -- clause 3 (Lemma 79c at `Hon'`)
    exact (lem79c_honestChainExtends_confirmations_step M F U) S A x R GST s' Hon' (Hs (s' + 1)) B E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hOwner (le_trans hGST hcc) h1 hHonUpd' hHonTick' hHs' hVotersV hFv

open Classical in
/-- **Kit theorem, the slot invariant through the round, over per-slot sets.** With the member
sets `Hon s'` shrinking from slot to slot, each awake and honest through its slot's update and not
past the start of slot `s₂ + 2`, the honest voters of each slot in its set, the counts of each slot
read at its set, `StepFrameAt` relative to `B` at the members of `Hon (s' + 1)` for every slot `s'`
with `s' + 3 ≤ s₂ + 2`, and the voter's fork choice of slot `s₂ + 1` at the members of
`Hon (s₂ + 1)`: from `HonestChainExtends M S Sched x (Hon s) B s`, the invariant holds at slot `s₂`
for `Hon s₂`, and every slot-`(s₂ + 1)` vote of a member of `Hon (s₂ + 1)` is for a block it holds
on `B`'s chain.

Why: `lem79_step_sets` at each slot from `s` to `s₂ − 1`, then `lem79a_votes_step_sets` at `s₂`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s`: the first slot; `s₂`: the last slot the invariant is carried to; `Hon`: the
  member sets; `Hs`: the honest voters of each slot; `B`: the proposal.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s₂`:
`lem79a_votes_step_sets`, which the proof calls at slot `s₂`, reads them there; the steps before it read them up to
earlier cutoffs.

Read aloud: the honest chain extends `B` at every slot of the round for that slot's members, and the
votes of the round's last slot are on `B`'s chain. -/
theorem round_honestChainExtends_steps (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s s₂ : ℕ) (Hon Hs : ℕ → Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s₂`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s₂ →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hs₂ : s ≤ s₂)
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` tick to its vote time, active up to that tick from the trace's start or from their own
    -- tick to a clock value at most the duty window's start of slot `s'`
    (hHon : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    -- for every slot `s'` before the last, each member of slot `s'` runs the update of slot `s'`, and none is in the
    -- adversary set at a step where a validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s₂ + 2 → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s₂ + 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₂ + 1)))
          (S.C.t_ ((s₂ + 1) - 1) + 3 * S.C.Δ) (s₂ + 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).viable_heads ∧
            B.AncestorEq W))
    (hBase : HonestChainExtends M S A x (Hon s) B s) :
    HonestChainExtends M S A x (Hon s₂) B s₂ ∧
    ∀ u ∈ Hon (s₂ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s₂ + 1))).tree,
        vote = GoldfishVote.mk u (s₂ + 1) H_u.root ∧ B.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hv : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  -- the induction
  have key : ∀ d, s + d ≤ s₂ → HonestChainExtends M S A x (Hon (s + d)) B (s + d) := by
    intro d
    induction d with
    | zero => intro _; exact hBase
    | succ d ih =>
        intro hd
        have hcut : M.supportCutoff S.C (s + d + 1) ≤ M.supportCutoff S.C s₂ :=
          (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
        exact (lem79_step_sets M F U) S A x R GST (s + d) (Hon (s + d)) (Hon (s + d + 1)) Hs B E hNet hSkew hRedeliver
          Sy hΔs
          (fun k u c hk hc' => hRoots k u c hk (le_trans hc' hcut))
          hParent hOwner
          (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
            (Nat.le_add_right s d))) (ih (by omega))
          (hHonMono (s + d) (by omega) (by omega))
          (hHonUpd (s + d) (by omega) (by omega))
          (hHon (s + d + 1) (by omega) (by omega))
          (hHonUpd (s + d + 1) (by omega) (by omega))
          (hHonTick (s + d + 1) (by omega) (by omega))
          (hHs (s + d) (by omega) (by omega)) (hHs (s + d + 1) (by omega) (by omega))
          (fun w hw => (hVoters (s + d) (by omega) (by omega) w
            (hHonMono (s + d) (by omega) (by omega) hw)).1)
          (fun v hv' => (hVoters (s + d + 1) (by omega) (by omega) v hv').2)
          (fun w hw => (hStep (s + d) (by omega) (by omega) w hw).1)
          (fun w hw => (hStep (s + d) (by omega) (by omega) w hw).2.1)
          (fun v hv' => (hStep (s + d) (by omega) (by omega) v hv').2.2)
  obtain ⟨d, rfl⟩ : ∃ d, s₂ = s + d := ⟨s₂ - s, by omega⟩
  have hInv := key d le_rfl
  have hv1 := hv (s + d + 1)
  have hc1 := hc (s + d + 1)
  refine ⟨hInv, ?_⟩
  exact (lem79a_votes_step_sets M F U) S A x R GST (s + d) (Hon (s + d)) (Hon (s + d + 1)) (Hs (s + d))
    B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (Nat.le_add_right s d))) hInv
    (hHonMono (s + d) (by omega) (by omega))
    -- the voters of slot `s₂`, updaters of slot `s₂`, are honest at the vote time of slot `s₂ + 1`, before their
    -- ticks to the support cutoff of slot `s₂ + 1`
    (fun u hu => (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
      (hHonUpd (s + d) (by omega) (by omega) u (hHs (s + d) (by omega) (by omega) u hu).1)
      (by
        have hR : ((M.voteTime S.C (s + d + 1) : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C (s + d + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.voteTime S.C (s + d + 1) + Δ S = M.supportCutoff S.C (s + d + 1) by omega)
        have hsk := hSkew
        have hB0 := E.behind_nonneg
        linarith))
    (fun v hv => (core_window_of_dutyWindow_reader M F U) x R E hΔs hSkew
      (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (Nat.le_add_right s d)))
      (hHon (s + d + 1) (by omega) (by omega) v hv))
    (hHs (s + d) (by omega) (by omega))
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew
      (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (Nat.le_add_right s d)))
      (hHonUpd (s + d) (by omega) (by omega) u (hHs (s + d) (by omega) (by omega) u hu).1))
    (fun w hw => (hVoters (s + d) (by omega) (by omega) w
      (hHonMono (s + d) (by omega) (by omega) hw)).1)
    (fun w hw => (hStepLast w hw).1) (fun w hw => (hStepLast w hw).2)

omit F in
/-- **Kit theorem, the holder row gives the sync fact's holder premises.** A validator active in every
configuration in force at a real time of `[tq, tq + δ]`, with `0 ≤ δ` and the time monotone, is active
in every configuration in force at `tq`, and active after every step whose real time is in
`[tq, tq + δ]`: the two premises the sync fact `SyncedWithinBy` asks of a holder read at `tq` with
`ΔHolderOnline = δ`.

The variables:
- `A`: the activity; `x`: the trace; `htime`: the time is monotone; `tq`: the time the sync fact is
  read at; `δ`: the holder's online delay; `v`: the holder.

Read aloud: a validator active through `δ` after `tq` is active at `tq` and after every step of that
window. -/
theorem holder_row_of_window {Msg N : Type}
    (A : Activity V) (x : Trace V Msg N) (htime : Monotone x.time) (tq : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    {v : V} (hv : v ∈ A.activeThroughout x tq (tq + δ)) :
    v ∈ A.activeAtTime x tq ∧
      ∀ i : ℕ, (tq : ℝ) ≤ x.time i → x.time i ≤ tq + δ → v ∈ A.active i :=
  ⟨Activity.mem_activeAtTime_of_mem_activeThroughout hv le_rfl (by linarith),
    fun i h1 h2 => Activity.mem_active_of_mem_activeThroughout_of_time htime hv h1 h2⟩

/-- **Kit theorem, an honest tick's attestation is delivered to a validator active from `tq`.**
The hypotheses of `attestation_in_pool_of_tick_send`; the conclusion is the delivery: some step `d`
before `q`'s last step before `c₁` delivers the attestation to `q`.

Why: when `tq ≤ t'`, synchrony from the send delivers it by `max t' GST + Δ_F`
(`delivered_before_stepBefore_of_honest_send_sync`), to `q`, active since the send. When `t' < tq`,
`v` holds the attestation from its tick on (`tick_holds_sent`), serves it at `tq`, and the sync fact
read at `tq` delivers it before `c₁`. The delivery half of
`attestation_in_pool_of_tick_send`, which calls it; the kit theorem
`attestations_reach_opener_of_sync` reads it for the corollary of Lemma 98 with the sync fact
.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time from
  which the network is synchronous; `tsend`: the bound on the time of the send; `c₁`: the time the
  delivery is before; `tq`: the time from which `q` is active; `q`: the receiver; `E`, `E_F`: the
  delivery promises; `Sy_F`: the sync fact for attestations, with the sync delay `Δs_F`; `hWS`: the
  trace is wake-shaped;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation.

Read at `q`'s own tick: `kQ` is `q`'s tick to the clock value `c₁`, `q` is active
at every step from the real time `tq` up to it, and the case split is on the real time
`x.time j` of the send, the one time the delivery promise speaks of.

Read aloud: an attestation an honest validator sent at its tick is delivered, before `c₁`, to every
validator active from `tq` to `c₁`, when the sender still serves it at `tq` in case it sent it
earlier. -/
theorem attestation_delivered_of_tick_send (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tsend c₁ : ℕ) (tq : ℝ) (q : V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hGST : GST ≤ tsend) (ht₁ : tsend + Δ_F S ≤ c₁)
    -- `c₁` is at least one FG delay or one sync delay after `GST` and after `tq`
    (hGSTq : GST + max (Δ_F S) Δs_F ≤ c₁) (htq : tq + ((max (Δ_F S) Δs_F : ℕ) : ℝ) ≤ c₁)
    (kQ : ℕ) (hkQ : x.lbl kQ = Event.tick q c₁)
    (hwin : ∀ i : ℕ, tq ≤ x.time i → i ≤ kQ → q ∈ A.active i)
    (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = Event.tick v t') (ht' : t' ≤ tsend)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    -- when the tick is before `tq`: `v` is active through the sync delay after the clock value `⌈tq⌉₊` (the sync
    -- fact's holder premise,) and serves `a` at its last step before `tq`
    (hvq : x.time j < tq → v ∈ A.activeThroughout x tq ((⌈tq⌉₊ : ℝ) + Δs_F))
    (hselq : x.time j < tq → ∀ k : ℕ, x.time k < tq → tq ≤ x.time (k + 1) → M.justifiedHeight (x.st k v) ≤ a.h) :
    (∃ d : ℕ, x.lbl d = Event.deliver q ⟨v, NamedObject.attest a⟩ ∧ d < kQ) ∨
      (tq ≤ c₁ ∧ ∃ k : ℕ, x.time k < tq ∧ tq ≤ x.time (k + 1) ∧ a ∈ (x.st k q).attestationsHeld) := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hhon : v ∉ A.corrupted j := E.not_mem_corrupted_of_tick hl
  have hkeep : x.time (j + 1) = x.time j := R.time_keep j (by rw [hl]; exact nofun)
  obtain ⟨⟨-, hTj⟩, -, hTj1⟩ := (time_of_lbl_tick M) x R E hl
  have hkQt := (E.tick_active kQ q c₁ hkQ).2.1
  have hmx1 := le_max_left (Δ_F S) Δs_F
  have hmx2 := le_max_right (Δ_F S) Δs_F
  have ht'R : (t' : ℝ) ≤ tsend := by exact_mod_cast ht'
  have ht₁R : (tsend : ℝ) + Δ_F S ≤ c₁ := by exact_mod_cast ht₁
  have hGSTR : (GST : ℝ) ≤ tsend := by exact_mod_cast hGST
  have hmxR1 : ((Δ_F S : ℕ) : ℝ) ≤ ((max (Δ_F S) Δs_F : ℕ) : ℝ) := by exact_mod_cast hmx1
  have hmxR2 : ((Δs_F : ℕ) : ℝ) ≤ ((max (Δ_F S) Δs_F : ℕ) : ℝ) := by exact_mod_cast hmx2
  have htqF : tq + Δ_F S ≤ c₁ := by linarith
  by_cases hlate : tq ≤ x.time j
  · -- the send at a real time from `tq` on: the delivery promise, `q` active from the send by `hwin`
    left
    have hjk : j < kQ := (lt_of_time_lt M) x R (by linarith)
    have hdk : max (x.time (j + 1)) (GST : ℝ) + (ΔNet_F : ℝ) ≤ x.time kQ := by
      have : max (x.time (j + 1)) (GST : ℝ) ≤ (tsend : ℝ) + ΔClockBehind :=
        max_le (by linarith) (by linarith)
      linarith
    by_cases hdel : ∃ d₀ : ℕ, j < d₀ ∧ d₀ < kQ ∧ x.lbl d₀ = Event.deliver q ⟨v, NamedObject.attest a⟩
    · obtain ⟨d₀, -, h2, h3⟩ := hdel
      exact ⟨d₀, h3, h2⟩
    · obtain ⟨d, -, hdk', hld, -, -⟩ := E_F.delivered j kQ q ⟨v, NamedObject.attest a⟩ c₁
        (max (x.time (j + 1)) (GST : ℝ) + (ΔNet_F : ℝ)) ⟨hsent, hhon⟩
        (show fgObject (NamedObject.attest a) from trivial) hkQ hjk
        (fun i h1 h2 => hwin i (le_trans hlate (htime (show j ≤ i by omega))) h2) rfl hdk
        (fun _ j₀ _ _ _ hij₀ hl₀ _ hj₀k₁ hk₁k _ _ _ => absurd ⟨j₀, hij₀, by omega, hl₀⟩ hdel)
      exact ⟨d, hld, hdk'⟩
  · -- the send before `tq`: `v` holds `a` from its tick on, serves it at its last step before `tq`, and the sync
    -- fact read at `tq` (its holder premise from `hvq`,) delivers it before `kQ`, or `q` holds it already
    push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time j := (time_nonneg M) x R j
    have htq0 : 0 < tq := lt_of_le_of_lt h0 hlate
    -- the last step `k` before the real time `tq`
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, x.time k < tq ∧ tq ≤ x.time (k + 1) := by
      classical
      have hex : ∃ i : ℕ, tq ≤ x.time i := by
        obtain ⟨i, hi⟩ := E.time_div ⌈tq⌉₊
        exact ⟨i, le_trans (Nat.le_ceil tq) hi⟩
      have hspec : tq ≤ x.time (Nat.find hex) := Nat.find_spec hex
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
    have hv := hvq hlate
    have hu : v ∈ A.active k :=
      Activity.mem_activeAtTime.1 (Activity.mem_activeAtTime_of_mem_activeThroughout hv le_rfl
        (by have := Nat.le_ceil tq; have : (0 : ℝ) ≤ Δs_F := Nat.cast_nonneg _; linarith)) _ hk1.le hk2
    have hhold : ∀ i : ℕ, tq ≤ x.time i → x.time i ≤ (⌈tq⌉₊ : ℝ) + Δs_F → v ∈ A.active i :=
      fun i h1 h2 => Activity.mem_active_of_mem_activeThroughout_of_time htime hv h1 h2
    obtain ⟨n', sent, hok, hst, hsentL⟩ := R.tick j v t' hl
    have hmem : NamedObject.attest a ∈ sent := by
      rw [hsentL, add_tsub_cancel_left] at hsent
      obtain ⟨m', hm', heq⟩ := Multiset.mem_map.1 hsent
      injection heq with _ hmo
      subst hmo
      exact Multiset.mem_coe.1 hm'
    have hInv := (lem11_node_invariant M F S A x R E j v hhon).1
    have hok' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.st j v) (t' : Int) := hok
    have hheld : a ∈ (x.st (j + 1) v).attestationsHeld := by
      rw [hst]
      exact (F.tk3.tick_holds_sent S.C S.P S.X (x.st j v) (t' : Int) n' sent hok' hInv).2 a hmem
    have hjq : j < k := by
      by_contra hjk
      push_neg at hjk
      have := htime (show k + 1 ≤ j + 1 by omega)
      linarith
    have hheldq : a ∈ (x.st k v).attestationsHeld :=
      (pool_grows_of_le M F) x R E v (by omega) a hheld
    -- the clock value `⌈tq⌉₊` plus the sync delay is at most `c₁`
    have hceil : ⌈tq⌉₊ + Δs_F ≤ c₁ := by
      have hle : Δs_F ≤ c₁ := by omega
      have h1 : tq ≤ ((c₁ - Δs_F : ℕ) : ℝ) := by
        rw [Nat.cast_sub hle]; linarith
      have := Nat.ceil_le.2 h1
      omega
    have hdl : max ⌈tq⌉₊ GST + Δs_F ≤ c₁ := by
      rcases le_total ⌈tq⌉₊ GST with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    rcases Sy_F tq k v q (NamedObject.attest a) (max ⌈tq⌉₊ GST + Δs_F) c₁ kQ hk1 hk2 hu
        ⟨hheldq, hselq hlate k hk1 hk2⟩ (show fgObject (NamedObject.attest a) from trivial)
        hhold rfl hkQ hdl
        (fun i h1 h2 => hwin i h1 h2)
        -- an attestation has no release clock value: the re-delivery premise is empty
        (fun _ _ _ _ hrel => absurd hrel (by simp [releaseOf])) with
      hqA | ⟨d, -, -, -, -, hld, hdk, -, -⟩
    · refine Or.inr ⟨by have : (0 : ℝ) ≤ ((max (Δ_F S) Δs_F : ℕ) : ℝ) := Nat.cast_nonneg _; linarith,
        k, hk1, hk2, hqA.1⟩
    · exact Or.inl ⟨d, hld, hdk⟩

/-- **Kit theorem, an honest tick's attestation reaches a validator active from `tq`.** An
attestation that `v`, honest at the time `t' ≤ tsend` of its tick, put on the wire at that tick is
held by `q` before `c₁`, when `q` is active from `tq` through `c₁`, `GST ≤ tsend`,
`tsend + Δ_F ≤ c₁`, and `c₁` is at least one FG delay or one sync delay after both `GST` and `tq`;
when the tick is before `tq`, `v` is also active through the sync delay `Δs_F` after `tq` and still serves the attestation there
(its justified height just before `tq` at most the attestation's height).

Why: when `tq ≤ t'`, synchrony from the send delivers it by `max t' GST + Δ_F`
(`delivered_before_stepBefore_of_honest_send_sync`), to `q`, active since the send. When `t' < tq`,
`v` holds the attestation from its tick on (`tick_holds_sent`), serves it at `tq`, and the sync fact
read at `tq` delivers it before `c₁`. The pool admits a
well-formed attestation, and only grows.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time from
  which the network is synchronous; `tsend`: the bound on the time of the send; `c₁`: the time the
  pool is read before; `tq`: the time from which `q` is active; `q`: the receiver; `E`, `E_F`: the
  delivery promises; `Sy_F`: the sync fact for attestations, with the sync delay `Δs_F`; `hWS`: the
  trace is wake-shaped;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation.

Read at `q`'s own tick: `kQ` is `q`'s tick to the clock value `c₁`, `q` is active
at every step from the real time `tq` up to it, and the case split is on the real time
`x.time j` of the send, the one time the delivery promise speaks of.

Read aloud: an attestation an honest validator sent at its tick is in the pool, before `c₁`, of
every validator active from `tq` to `c₁`, when the sender still serves it at `tq` in case it sent it
earlier. -/
theorem attestation_in_pool_of_tick_send (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tsend c₁ tq : ℕ) (q : V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hGST : GST ≤ tsend) (ht₁ : tsend + Δ_F S ≤ c₁)
    -- `c₁` is at least one FG delay or one sync delay after `GST` and after `tq`
    (hGSTq : GST + max (Δ_F S) Δs_F ≤ c₁) (htq : tq + max (Δ_F S) Δs_F ≤ c₁)
    (kQ : ℕ) (hkQ : x.lbl kQ = Event.tick q c₁)
    (hwin : ∀ i : ℕ, (tq : ℝ) ≤ x.time i → i ≤ kQ → q ∈ A.active i)
    (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = Event.tick v t') (ht' : t' ≤ tsend)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    -- when the tick is before `tq`: `v` is active through the sync delay after `tq` (the sync fact's holder
    -- premise,) and serves `a` there
    (hvq : x.time j < tq → v ∈ A.activeThroughout x tq (tq + Δs_F))
    (hselq : x.time j < tq → M.justifiedHeight (x.stateBefore tq v) ≤ a.h) :
    a ∈ (x.st kQ q).attestationsHeld := by
  have hWF := (tick_attestation_well_formed M F) S A x R E j t' v a hl hsent
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hkQt := (E.tick_active kQ q c₁ hkQ).2.1
  have hΔF : (Δ_F S : ℝ) ≤ max (Δ_F S) Δs_F := by exact_mod_cast le_max_left _ _
  have htqR : ((tq : ℕ) : ℝ) + max (Δ_F S) Δs_F ≤ c₁ := by exact_mod_cast htq
  -- the kit reads `q`'s and `v`'s states at the last step before the real time `tq`, here `x.stepBefore tq`
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hlast : ∀ k : ℕ, x.time k < (tq : ℝ) → (tq : ℝ) ≤ x.time (k + 1) → k = x.stepBefore tq := by
    intro k hk1 hk2
    have htq1 : 1 ≤ tq := by
      have h0 : (0 : ℝ) ≤ x.time k := (time_nonneg M) x R k
      have : (0 : ℝ) < (tq : ℝ) := lt_of_le_of_lt h0 hk1
      exact_mod_cast this
    obtain ⟨hb1, hb2⟩ := (stepBefore_time M) x R E htq1
    rcases lt_trichotomy k (x.stepBefore tq) with h | h | h
    · have := htime (show k + 1 ≤ x.stepBefore tq by omega); linarith
    · exact h
    · have := htime (show x.stepBefore tq + 1 ≤ k by omega); linarith
  rcases (attestation_delivered_of_tick_send M F) S A x R GST tsend c₁ (tq : ℝ) q E hNet hSkew hRedeliver E_F hNet_F
    hSkew_F Sy_F hGST ht₁ hGSTq (by exact_mod_cast htq) kQ hkQ hwin j t' v a hl ht' hsent
    (fun h => by rw [Nat.ceil_natCast]; exact hvq h)
    (fun h k hk1 hk2 => by rw [hlast k hk1 hk2]; exact hselq h) with
    ⟨d, hld, hd⟩ | ⟨-, k, hk1, hk2, hheld⟩
  swap
  rw [hlast k hk1 hk2] at hheld
  · -- `q` already holds `a` before `tq`, a real time before its tick `kQ`
    have hle : x.stepBefore tq ≤ kQ := by
      by_contra hlt
      push_neg at hlt
      have h1 := ((lt_stepBefore_iff M) x R E).1 hlt
      have h2 : x.time kQ ≤ x.time (kQ + 1) := R.time_mono (Nat.le_succ kQ)
      linarith
    exact (pool_grows_of_le M F) x R E q hle a hheld
  obtain ⟨-, hstep⟩ := (deliver_step_state M F) x R E hld
  have hin : a ∈ (x.st (d + 1) q).attestationsHeld := by
    rw [hstep]
    exact F.rcv.receive_attestation_held S.C S.P S.X _ a hWF
  exact (pool_grows_of_le M F) x R E q hd a hin

/-- **Kit theorem, the round's attestations reach the next proposer.** Write `a` for the support
cutoff of slot `s + 1`, and `H`, `T` for the height of `B`'s chain state and the root of its `T_h`.
In an execution where every time is reached, corruption is permanent and attestations are delivered
within `Δ_F` after `GST`: if `GST` is at most `a`, `a + Δ_F` is at most `c₁`, `B` is of slot `s`;
and for every member `v` of `Q`: `v` is awake and honest from the duty window's start of slot
`s + 1` to `a`, every outcome of its tick at `a`, from its state awake for slot `s + 1`, saves `B`
as the confirmation of slot `s` with `B` among its fast blocks, every live lock entry an outcome of
its tick at the vote time of slot `s + 1` leaves, from its state awake for that slot, is compatible
with `B`, its frame before `a` has the root `ρ v`, `B` or an ancestor of `B`, and the
`head_height_floor` `φ v`, at most `H`, it holds `B` before `a`, and its cache `h_j` is less than
`H`, or no lock at `H`, or its lock at `H` is `T`; and `q` is awake and honest from `tq` to `c₁`,
with `tq + Δ_F ≤ c₁` — then `q`'s pool before `c₁` holds an attestation of every member of `Q` at
`H` naming `T`; and when no member's record before `a` holds anything sent at `H`, a target of each.

Why: Lemma 61 at each member; an attestation already sent is traced to the tick that sent it
(`record_content_sent`); with nothing sent at `H`, Lemma 55's corollary. Each reaches `q` by
synchrony or by the catch-up on `q`'s last wake (`delivered_before_stepBefore_of_honest_send`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `c₁`: the time of the next proposal; `tq`:
  the time from which `q` is awake and honest;
- `Q`: the quorum; `B`: the proposal; `q`: the next proposer; `φ v`, `ρ v`: the
  `head_height_floor` and the root of member `v`'s frame before `a`.

Read at the validators' own ticks: each member's update, locks, frame, tree and
record are read in the state its tick to the support cutoff of slot `s + 1` (its locks: to the
vote time of slot `s + 1`) starts from, each member ticks to that cutoff active from the trace's
start or from its own tick to a clock value at most `duty_window_start S.C (s + 1)`, and `q`'s
pool is read in the state its tick `kQ` to the clock value `c₁` starts from, `q` active at every
step from the real time `tq` up to that tick.

Read aloud: every member of `Q` attests for `B`'s height and `T_h` root, and the attestation is in
the next honest proposer's pool before its slot starts. -/
theorem round_attestations_in_pool (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r s c₁ tq : ℕ) (Q : Finset V) (B : Block V) (q : V)
    (φ : V → Height) (ρ : V → Block V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hs : s = r * S.C.R)
    (hGST : GST ≤ M.supportCutoff S.C (s + 1))
    (ht₁ : M.supportCutoff S.C (s + 1) + Δ_F S ≤ c₁)
    (hBslot : B.slot = s)
    (hv : ∀ v ∈ Q, v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hUpd : ∀ v ∈ Q, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) →
      M.savedConfirmation n' s = some B ∧ B ∈ M.fastBlocks n')
    (hLocks : ∀ v ∈ Q, ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hShape : ∀ v ∈ Q, FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρ v) (φ v))
    (hRoot : ∀ v ∈ Q, (ρ v).AncestorEq B)
    (hBin : ∀ v ∈ Q, B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree)
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    (hBHeight : ∀ v ∈ Q, φ v ≤ (M.chainStateOf S.C B).h)
    -- `c₁` is at least one FG delay or one sync delay after `GST` and after `tq`
    (hGSTq : GST + max (Δ_F S) Δs_F ≤ c₁)
    (htq : tq + max (Δ_F S) Δs_F ≤ c₁)
    (kQ : ℕ) (hkQ : x.lbl kQ = Event.tick q c₁)
    (hwin : ∀ i : ℕ, (tq : ℝ) ≤ x.time i → i ≤ kQ → q ∈ A.active i)
    -- every member is active through the sync delay after `tq` (the sync fact's holder premise,;
    --, and its justified height just before `tq` is at most `H`
    (hvq : ∀ v ∈ Q, v ∈ A.activeThroughout x tq (tq + Δs_F))
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore tq v) ≤ (M.chainStateOf S.C B).h) :
    (∀ u ∈ Q, ∃ a ∈ (x.st kQ q).attestationsHeld,
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      ∀ u ∈ Q, ∃ a ∈ (x.st kQ q).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧
        a.T = (M.chainStateOf S.C B).T_h.root ∧ a.τ = false) := by
  -- an attestation a member sent at a tick to a clock value at most the support cutoff of slot `s + 1`, at `H`, is
  -- in `q`'s pool at its tick `kQ` (the holder row `hvq`,)
  have hDeliver : ∀ (j t' : ℕ) (v : V) (a : Attestation V), v ∈ Q → a.h = (M.chainStateOf S.C B).h →
      x.lbl j = Event.tick v t' → t' ≤ M.supportCutoff S.C (s + 1) →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      a ∈ (x.st kQ q).attestationsHeld := by
    intro j t' v a hvQ hah hl ht' hsent
    exact (attestation_in_pool_of_tick_send M F) S A x R GST (M.supportCutoff S.C (s + 1)) c₁ tq q
      E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy_F hGST ht₁ hGSTq htq kQ hkQ hwin j t' v a hl ht' hsent
      (fun _ => hvq v hvQ) (fun _ => by rw [hah]; exact hselq v hvQ)
  -- an outcome of each member's tick to the support cutoff of slot `s + 1`, from its state awake for that slot (the
  -- member's reader from `duty_window_start S.C (s + 1)`)
  have hDuty : duty_window_start S.C (s + 1) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (s + 1)
  have hOut : ∀ u ∈ Q, ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput u (M.supportCutoff S.C (s + 1))) (s + 1) := by
    intro u hu
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hv u hu)
    obtain ⟨n'', sent, hrun, hAw, -⟩ := (update_state_of_tick M F U) S A x R s u E hk
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E (hv u hu) hDuty)
    exact ⟨n'', sent, hrun, hAw⟩
  refine ⟨fun u hu => ?_, fun hFresh u hu => ?_⟩
  · obtain ⟨n', sent, hrun, hA⟩ := hOut u hu
    obtain ⟨hS, hF⟩ := hUpd u hu n' sent hrun hA
    have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew (hv u hu) n' sent
      hrun hA hS hBslot (hLocks u hu)
    rcases (lem61_honest_validator_attests_frame M F U) S A x R r s B u (ρ u) (φ u) E hs (hv u hu)
        n' sent hrun hA hS hF hLk (hShape u hu) (hRoot u hu) (hBHeight u hu) (hBin u hu) (hLockBox u hu)
      with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
    · exact ⟨a, hDeliver i _ u a hu hah hl le_rfl hsent, hav, hah, haT⟩
    · obtain ⟨j, t', a, hl, ht', -, hsent, hav, hac, -⟩ := (record_content_sent M F) S A x R _ u b E hb
      have hah' : a.h = (M.chainStateOf S.C B).h := by rw [← hbh, ← hac]; rfl
      refine ⟨a, hDeliver j t' u a hu hah' hl ht'.le hsent, hav, hah', ?_⟩
      rw [← hbT, ← hac]
      rfl
  · obtain ⟨n', sent, hrun, hA⟩ := hOut u hu
    obtain ⟨hS, hF⟩ := hUpd u hu n' sent hrun hA
    have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew (hv u hu) n' sent
      hrun hA hS hBslot (hLocks u hu)
    -- Lemma 55's viable-tree and record hypotheses at `u`'s tick input (as `lem61_honest_validator_attests_frame`)
    have hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput u (M.supportCutoff S.C (s + 1))))
        (M.fg_to_ac (x.tickInput u (M.supportCutoff S.C (s + 1)))).tree := by
      refine (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_of_frameShape_of_core M F) S.C S.P S.X _
        (lem11_node_invariantCore_of_run M F S x R (x.tickStep u (M.supportCutoff S.C (s + 1))) u).1 (ρ u) (φ u) B
        (hShape u hu) ?_ (hRoot u hu) (hBin u hu) (hBHeight u hu)
      rw [← (hShape u hu).1]
      exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ u
    have hRecord : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root) := by
      rcases hLockBox u hu with hlt | hnone | hlock
      · exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.lock_none_of_h_j_lt_of_exec M F) S A x R E _ u _ hlt)
      · exact Or.inl hnone
      · exact Or.inr ⟨hlock, (GoldilocksCorrectness.Record.Statements.Executions.lockNamesSent_of_exec M F) S A x R E _ u _ _
          hlock⟩
    obtain ⟨i, a, hl, hsent, hav, hah, haT, hτ⟩ := (lem55_target_of_fresh_height M F U) S A x R r s B u E hs
      (hv u hu) n' sent hrun hA hS hF hLk hViable hRecord (hFresh u hu)
    exact ⟨a, hDeliver i _ u a hu hah hl le_rfl hsent, hav, hah, haT, hτ⟩

/-- **Kit theorem, the next honest proposal extends the round's proposal.** Write `t₁` for the
start of slot `s₂ + 2`. In an execution with the eight execution assumptions: if `GST` is at most
the vote time of slot `s₂ + 1`; `HonestChainExtends M S Sched x Hon B s₂` holds; every
slot-`(s₂ + 1)` vote of a member of `Hon` is for a block it holds on `B`'s chain; `q` is a member
that ran the update of slot `s₂` awake up to its own tick (`updaterAt`); every member of `Hs` is a
member of `Hon` and of the slot-`(s₂ + 1)` committee voting at that slot, active through the sync delay after Lemma
12's read time of slot `s₂ + 1` and outside the adversary set at `q`'s tick to the start of slot `s₂ + 2`; the slot-`(s₂ + 1)` voters `q`'s proposal counts are fewer than twice `Hs`; `q`'s fork-choice
root before `t₁` is compatible with `B` and, when it is `B` or an ancestor of `B`, a block of `q`'s
frame tree that is `B` or a descendant of `B` is a viable head; and `q` put `B'` on the wire at its
tick at `t₁` — then `B` is `B'`'s parent or an ancestor of it.

Why: `q`'s anchor is compatible with `B` (Lemma 6: its live locks by the invariant, its root by
hypothesis) and is `B'`'s parent or an ancestor of it. When the anchor is an ancestor of `B`, the
slot-`(s₂ + 1)` majority's votes, all on `B`'s chain, take `q`'s walk past `B`
(`proposal_parent_extends_majority_block`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s₂`: the slot of the invariant; `Hon`: the members; `Hs`: the honest voters of
  slot `s₂ + 1`; `B`: the round's proposal; `B'`: `q`'s proposal; `q`: its proposer.

Roots name blocks until `M.supportCutoff S.C (s₂ + 1)`: `proposal_parent_extends_majority_block`,
which the proof calls at slot `s₂ + 1`, takes blocks as held up to the support cutoff of slot
`s₂ + 1`.

Read aloud: the next honest proposal's parent is `B` or a descendant of `B`. -/
theorem round_proposal_extends (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₂ : ℕ) (Hon Hs : Finset V) (B B' : Block V)
      (q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to the real time of `q`'s tick to the support cutoff of slot `s₂ + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep q (M.supportCutoff S.C (s₂ + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s₂ + 1))
    (hInv : HonestChainExtends M S A x Hon B s₂)
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s₂ + 1))).tree,
        vote = GoldfishVote.mk u (s₂ + 1) H_u.root ∧ B.AncestorEq H_u)
    (hq : q ∈ Hon)
    -- `q` runs the update of slot `s₂` awake up to its own tick
    (hqUpd : q ∈ updaterAt M S A x s₂)
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s₂ + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₂ + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the voters of slot `s₂ + 1` are active through the sync delay after Lemma 12's read time of slot `s₂ + 1`, and
    -- outside the adversary set at `q`'s tick to the start of slot `s₂ + 2`
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHonest : ∀ u ∈ Hs, u ∉ A.corrupted (x.tickStep q (M.slotStart S.C (s₂ + 2))))
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C (s₂ + 2)))
        (s₂ + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hFrameQ :
        (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).viable_heads ∧
            B.AncestorEq W))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C (s₂ + 2)) ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B'.parent := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss₂ : M.slotStart S.C (s₂ + 2) = M.slotStart S.C (s₂ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₂ + 1), show s₂ + 2 = s₂ + 1 + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hv₁ : M.voteTime S.C (s₂ + 1) = M.slotStart S.C (s₂ + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₂ + 1)
  have hv₂ : M.voteTime S.C (s₂ + 2) = M.slotStart S.C (s₂ + 2) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₂ + 2)
  have hc₁ : M.supportCutoff S.C (s₂ + 1) = M.voteTime S.C (s₂ + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₂ + 1)
  obtain ⟨i, hl, hsent⟩ := hPropose'
  have hAnc := (get_anchor_ancestorEq_proposal_parent M F) S A x R E (s₂ + 2) i B' q hl hsent
  -- `q`'s tick to the vote time of slot `s₂ + 1`, inside its update reader
  have hqR := (vote_reader_from_updater_under_skew M F U) S A x R s₂ q E hSkew hqUpd
  -- `q`'s anchor at its tick input is compatible with `B`
  have hAC : (M.get_anchor (x.tickInput q (M.slotStart S.C (s₂ + 2)))
      ((M.slotStart S.C (s₂ + 2) : ℕ) : Int)).compatible B = true := by
    refine (GoldilocksCorrectness.Record.Statements.Routines.lem6_get_anchor_compatible M F) _ _ B
      (fun e he hlive => ?_) hFrameQ.1
    refine (live_locks_compatible_of_honestChainExtends_tick M F U) S A x R Hon B s₂ (M.slotStart S.C (s₂ + 2))
      q E hInv hq hqR (by omega) (by omega) e he ?_
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive
    exact hlive.1
  rcases (compatible_iff _ _).1 hAC with hAB | hBA
  · -- the anchor is an ancestor of `B`: the majority's walk passes `B`
    have hchoose : ∀ u : V, ∃ Hu : Block V, u ∈ Hs →
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₂ + 1)) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₂ + 1) Hu.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
        Hu ∈ (x.tickInput u (M.voteTime S.C (s₂ + 1))).tree ∧ B.AncestorEq Hu := by
      intro u
      by_cases hu : u ∈ Hs
      · obtain ⟨huH, -, vote, -, -, i', hl', hs'⟩ := hHs u hu
        obtain ⟨Hu, hHuT, hvote, hBH⟩ := hVotes u huH vote ⟨i', hl', hs'⟩
        rw [hvote] at hs'
        exact ⟨Hu, fun _ => ⟨⟨i', hl', hs'⟩, hHuT, hBH⟩⟩
      · exact ⟨B, fun h => absurd h hu⟩
    choose Hf hHf using hchoose
    have hρB : (M.fg_to_ac (x.tickInput q (M.slotStart S.C (s₂ + 2)))).fc_root.AncestorEq B :=
      ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) hAB
    exact ((proposal_parent_extends_majority_block M F U) S A x R GST (s₂ + 1) i Hs Hf B B' q E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hOwner hGST
      (fun u hu => ⟨(hHs u hu).2.1, hHonest u hu, (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2⟩)
      hVotersQ hHold ((updater_reader_gives_own_core_window M F U) x R E hΔs hSkew hqUpd)
      hl hsent (hFrameQ.2 hρB) hAB).1
  · exact ancestorEq_trans hBA hAnc

/-- **Kit fact, a voter's fork choice from its frame shapes over the window.** When `w`'s frame
has the root `ρ j` and the `head_height_floor` `φ` at every step `j` from `w`'s tick to the start of
slot `s` to its tick to the start of slot `s''`, the root is compatible with `B` at every step after
`w`'s tick to the vote time of slot `s`, `w` holds `B` in the state that tick starts from, and `B`'s
height is at least `φ`: for every slot `s'` with `s ≤ s'` and `s' + 2 ≤ s''`, `w`'s fork-choice root
in the state its tick to the vote time of slot `s' + 1` starts from is compatible with `B` and, when
it is `B` or an ancestor of `B`, `B` is in `w`'s voter tree of slot `s' + 1` and is a viable head.
`w` ticks to the start of slot `s''`, active at every step up to that tick from the trace's start or
from its own tick to a clock value at most `duty_window_start S.C s`, and the clock
bounds are less than one delay together (`hSkew`).

Why: the reader gives `w`'s ticks to the vote times of slots `s` and `s' + 1`, inside its window by
more than both clock bounds (`mem_activeThroughoutToTick_of_inside`), ordered by their clock values
(`tick_lt_of_clock_lt`) before its tick to the start of slot `s''`. Lemma 56 reads the root off the
shape at the tick to the vote time of slot `s' + 1`; `proposal_viable_head_at_tick_st` gives the
viable head from `B` held at the tick to the vote time of slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`, `s''`: the window's slots; `s'`:
  the slot of the step; `w`: the voter; `B`: the block; `φ`, `ρ`: the `head_height_floor` and the
  roots of `w`'s frames, the roots indexed by step.

Read aloud: a voter whose frame shape holds at every step of the window has, at each of its ticks to
a vote time of the window, a fork-choice root compatible with `B` and, when that root is `B` or an
ancestor of `B`, `B` as a viable head of its voter tree. -/
theorem voterFrame_of_shape (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s s'' s' : ℕ) (w : V) (B : Block V) (φ : Height)
    (ρ : ℕ → Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hs' : s ≤ s') (hs'' : s' + 2 ≤ s'')
    -- `w` ticks to the start of slot `s''`, active up to that tick from the trace's start or from its
    -- own tick to a clock value at most `duty_window_start S.C s`
    (hw : w ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    (hShape : ∀ j : ℕ, x.tickStep w (M.slotStart S.C s) ≤ j → j ≤ x.tickStep w (M.slotStart S.C s'') →
      FrameShape M (x.st j w) (ρ j) φ)
    (hRootAfter : ∀ j : ℕ, x.tickStep w (M.voteTime S.C s) < j →
        j ≤ x.tickStep w (M.slotStart S.C s'') → (ρ j).compatible B = true)
    (hHeld : B ∈ (x.tickInput w (M.voteTime S.C s)).tree)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h) :
    (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true ∧
    ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
        (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
          B.AncestorEq W) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvs, -, -, -, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨hv1, -, -, hs2, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  rw [show s' + 1 + 1 = s' + 2 from rfl] at hs2
  obtain ⟨-, -, hf, hs1, -, -, -⟩ := (slot_times M F U) S s'
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hm1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S hs'
  have hm2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S hs''
  have hdw := duty_window_start_real S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  -- the clock values, as natural numbers and as reals
  have hn1 : M.voteTime S.C s + 3 * Δ S ≤ M.slotStart S.C s'' := by omega
  have hn2 : M.voteTime S.C (s' + 1) + 3 * Δ S ≤ M.slotStart S.C s'' := by omega
  have hn3 : M.voteTime S.C s < M.voteTime S.C (s' + 1) := by omega
  have hvsR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * Δ S * s + Δ S := by
    rw [hvs, hss]; push_cast; ring
  have hr1 : ((M.voteTime S.C s : ℕ) : ℝ) + 3 * Δ S ≤ M.slotStart S.C s'' := by exact_mod_cast hn1
  have hr2 : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) + 3 * Δ S ≤ M.slotStart S.C s'' := by
    exact_mod_cast hn2
  have hr3 : ((M.voteTime S.C s : ℕ) : ℝ) ≤ M.voteTime S.C (s' + 1) := by exact_mod_cast hn3.le
  have hdwR : ((duty_window_start S.C s : ℤ) : ℝ) + ΔClockBehind <
      ((M.voteTime S.C s : ℕ) : ℝ) - ΔClockAhead := by
    rw [hdw, hvsR]; linarith
  -- `w`'s ticks to the two vote times, inside the reader's window
  have hwv : w ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hw (by omega) hdwR (by linarith)
  have hw1 : w ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C (s' + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hw (by omega) (by linarith) (by linarith)
  obtain ⟨kv, hkv, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hwv hdwR
  obtain ⟨j₁, hj₁, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw1 hdwR
  obtain ⟨kE, hkE, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw hdwR
  have hkvj : kv < j₁ := (tick_lt_of_clock_lt M) x E hkv hj₁ hn3
  have hj₁E : j₁ < kE := (tick_lt_of_clock_lt M) x E hj₁ hkE (by omega)
  have htsv : x.tickStep w (M.voteTime S.C s) = kv := (tickStep_eq_of_lbl M) x E hkv
  have htsj : x.tickStep w (M.voteTime S.C (s' + 1)) = j₁ := (tickStep_eq_of_lbl M) x E hj₁
  have htsE : x.tickStep w (M.slotStart S.C s'') = kE := (tickStep_eq_of_lbl M) x E hkE
  -- the tick to the start of slot `s`, when there is one, is before `j₁`
  have hstart : x.tickStep w (M.slotStart S.C s) ≤ j₁ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨i, hi⟩ := x.exists_tick_of_lt_tickStep hlt
    rw [(tickStep_eq_of_lbl M) x E hi] at hlt
    have := (tick_lt_of_clock_lt M) x E hi hj₁ (by omega)
    omega
  have hsh := hShape j₁ hstart (by rw [htsE]; exact hj₁E.le)
  have hR := ((GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X
    (x.st j₁ w) (lem11_node_invariantCore_of_run M F S x R j₁ w).1 _ _ hsh).1
  have hti : x.tickInput w (M.voteTime S.C (s' + 1)) = x.st j₁ w := by
    show x.st (x.tickStep w (M.voteTime S.C (s' + 1))) w = x.st j₁ w
    rw [htsj]
  rw [hti]
  refine ⟨by rw [hR]; exact hRootAfter j₁ (by rw [htsv]; exact hkvj) (by rw [htsE]; exact hj₁E.le),
    fun hroot => ?_⟩
  rw [hR] at hroot
  have hlt : x.clockValue kv w < M.voteTime S.C s :=
    (clockValue_lt_of_tick_of_active M F) E hkv (by omega) hwinv
  have h := (proposal_viable_head_at_tick_st M F U) S A x R (M.voteTime S.C s) (s' + 1) w B (ρ j₁) φ E
    kv j₁ hkv hlt hkvj.le (E.not_mem_corrupted_of_tick hj₁) hHeld
    (by rw [Nat.add_sub_cancel, hf]; omega) hsh hroot hBHeight
  exact ⟨B, by classical exact (Finset.mem_filter.1 h.1).2, h.2, ancestorEq_refl B⟩

/-- **Kit fact, a proposer's fork choice from its frame shape.** When `q`'s frame before `t` has
the root `ρ`, compatible with `B`, and the `head_height_floor` `φ`, at most `B`'s height, and `q`
holds `B` before `t`: `q`'s fork-choice root before `t` is compatible with `B`, and when it is `B`
or an ancestor of `B`, `B` is in `q`'s frame tree and is a viable head.

Why: Lemma 56; `B`'s chain state in `q`'s state is its own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `q`: the proposer;
  `B`: the block; `ρ`, `φ`: the root and the `head_height_floor` of `q`'s frame.

Read aloud: a proposer whose frame shape holds has a fork-choice root compatible with `B` and, when
that root is `B` or an ancestor of `B`, `B` as a viable head of its frame tree. -/
theorem proposerFrame_of_shape (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (q : V) (B ρ : Block V) (φ : Height)
    (hShape : FrameShape M (x.stateBefore t q) ρ φ)
    (hRoot : ρ.compatible B = true)
    (hBq : B ∈ (x.stateBefore t q).tree)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h) :
    (M.fg_to_ac (x.stateBefore t q)).fc_root.compatible B = true ∧
    ((M.fg_to_ac (x.stateBefore t q)).fc_root.AncestorEq B →
      ∃ W ∈ (M.fg_to_ac (x.stateBefore t q)).tree,
        W ∈ (M.fg_to_ac (x.stateBefore t q)).viable_heads ∧ B.AncestorEq W) := by
  have hR : (M.fg_to_ac (x.stateBefore t q)).fc_root = ρ := 
    ((GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X (x.stateBefore t q)
      (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) q).1 _ _ hShape).1
  refine ⟨by rw [hR]; exact hRoot, fun hρB => ?_⟩
  have hFB : (x.stateBefore t q).finalized.AncestorEq B :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E _ q)
      (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hρB)
  rw [hR] at hρB
  have hVH : B ∈ (M.fg_to_ac (x.stateBefore t q)).viable_heads := by
    exact (((GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X (x.stateBefore t q)
      (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) q).1 _ _ hShape).2.2 B).2
      ⟨hBq, hFB, hρB, hBHeight⟩
  exact ⟨B, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBq, hFB⟩, hVH, ancestorEq_refl B⟩

/-- **Kit lemma, the proposer's fork choice from a frame shape at a step.** As `proposerFrame_of_shape`, read at the
state `x.st j q` of a step `j` (a tick input) instead of at the state before a time: when `q`'s node state at step `j`
has the frame shape `(ρ, φ)`, `ρ` is compatible with `B`, `q` holds `B` and `φ` is at most the chain-state height of
`B`, then `q`'s fork-choice root at that state is compatible with `B`, and when that root is `B` or an ancestor of `B`,
some block of `q`'s frame tree that is `B` or a descendant of `B` is a viable head.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `j`: the step; `q`: the validator;
  `B`: the block; `ρ`: the root of the frame shape; `φ`: its `head_height_floor`.

Read aloud: a frame shape at `q`'s state at step `j` whose root is compatible with `B`, with `B` held and high enough,
gives `q`'s fork choice there the two facts a proposal on `B`'s chain needs. -/
theorem proposerFrame_of_shape_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (j : ℕ) (q : V) (B ρ : Block V) (φ : Height)
    (hShape : FrameShape M (x.st j q) ρ φ)
    (hRoot : ρ.compatible B = true)
    (hBq : B ∈ (x.st j q).tree)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h) :
    (M.fg_to_ac (x.st j q)).fc_root.compatible B = true ∧
    ((M.fg_to_ac (x.st j q)).fc_root.AncestorEq B →
      ∃ W ∈ (M.fg_to_ac (x.st j q)).tree,
        W ∈ (M.fg_to_ac (x.st j q)).viable_heads ∧ B.AncestorEq W) := by
  have hR : (M.fg_to_ac (x.st j q)).fc_root = ρ :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X (x.st j q)
      (lem11_node_invariantCore_of_run M F S x R j q).1 _ _ hShape).1
  refine ⟨by rw [hR]; exact hRoot, fun hρB => ?_⟩
  have hFB : (x.st j q).finalized.AncestorEq B :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E j q)
      (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hρB)
  rw [hR] at hρB
  have hVH : B ∈ (M.fg_to_ac (x.st j q)).viable_heads := by
    exact (((GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape_of_core M F) S.C S.P S.X (x.st j q)
      (lem11_node_invariantCore_of_run M F S x R j q).1 _ _ hShape).2.2 B).2
      ⟨hBq, hFB, hρB, hBHeight⟩
  exact ⟨B, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBq, hFB⟩, hVH, ancestorEq_refl B⟩

open Classical in
/-- Lemma 80 over per-slot member sets, with the frames read at the first slot's three reading
points, the step conditions per slot after the action time, and `q`'s fork choice before its
proposal. The proof; the audited statement is in `Statements/Executions/RoundStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: `round_proposal_extends`, which the proof
calls at the slot `s'' - 2`, takes blocks as held up to the support cutoff of slot `s'' - 1`;
the base and the invariant through the round read earlier.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the round theorem asks of each slot's committee majority honesty through its own slot's
update only, reads the frames of the first slot at its three reading points, the chain's step
conditions after the action time, and the next proposer's fork choice at its proposal; then the next
honest proposal is on the round's proposal's chain with the height risen or the progress quorum on
chain. -/
theorem lem80wq_round_height_advances_steps (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
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
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape M (x.tickInput w (M.voteTime S.C s)) (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (M.chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (M.chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  -- the slots: `s'' = s₂ + 2`, with `s ≤ s₂`
  have hR := S.C.R_ge_two
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  rw [show s₂ + 2 - 1 = s₂ + 1 by omega] at hVotersQ hStepLast hq hRoots hHonLast hHonestQ
  -- the times
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : ∀ k, M.slotStart S.C (k + 1) = M.slotStart S.C k + 4 * Δ S := fun k => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hsE : ∀ k, M.slotStart S.C k = 4 * Δ S * k :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hv : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hsm : s - 1 + 1 = s := by omega
  have hk8 := (slot_times M F U S s).2.2.2.2.2.1
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the bound `hΔs` with the read time `max (2 * Δ S) Δs` of Lemma 12
  have hm2R : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
    rcases le_total (2 * Δ S) Δs with h2 | h2
    · rw [max_eq_right h2]
      have : max ((Δ S : ℕ) : ℝ) (Δs : ℝ) = Δs := max_eq_right (by exact_mod_cast (show Δ S ≤ Δs by omega))
      have h' := hΔs
      push_cast at h' ⊢
      rw [this] at h'
      exact h'
    · rw [max_eq_left h2]
      push_cast
      linarith
  have hm2 : max (2 * Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (2 * Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by push_cast; push_cast at hm2R; linarith
    exact_mod_cast h'
  have hm2s := le_max_right (2 * Δ S) Δs
  have hm2l := le_max_left (2 * Δ S) Δs
  have hvs0 := hv (s - 1)
  have hss0 : M.slotStart S.C s = M.slotStart S.C (s - 1) + 4 * Δ S := by rw [← hss (s - 1), hsm]
  have hvs := hv s
  have hss1 := hss s
  have hvs1 := hv (s + 1)
  have hcs1 := hc (s + 1)
  have hm2' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S (show s + 2 ≤ s₂ + 2 by omega)
  have ha : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C (s₂ + 2) := hs''
  have hcut₁ : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s₂ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hcut₂ : M.supportCutoff S.C s₂ ≤ M.supportCutoff S.C (s₂ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- `B` is of slot `s`
  have hPropose₀ : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    rw [hsm]
    exact hPropose
  obtain ⟨i₀, hl₀, hsent₀⟩ := hPropose₀
  have hBslot : B.slot = s := by
    rw [← hsm]
    exact ((proposal_parent_walk_end M F U) S A x R E (s - 1) i₀ B p hl₀ hsent₀).1
  -- step 1: the base, at the first slot's set, with the reader start `max tStart (duty_window_start S.C s)`: the
  -- members' readers open at the duty window's start of slot `s`, the proposer's at `tStart`
  have hdwle : duty_window_start S.C s ≤ max tStart (duty_window_start S.C s) := le_max_right _ _
  have htStart' : ((max tStart (duty_window_start S.C s) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total tStart (duty_window_start S.C s) with h | h
    · -- the duty window's start `st(s) + Δ − 4Δk` is more than both clock bounds before Lemma 12's read time of
      -- slot `s − 1`, truncated at `0` or not
      rw [max_eq_right h, duty_window_start_real S s]
      have i3A := E.ahead_nonneg
      have i3B := E.behind_nonneg
      have i3D : (0 : ℝ) ≤ Δ S := by positivity
      have i3k8 : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast (slot_times M F U S s).2.2.2.2.2.1
      have i3sE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
      have i3vT := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
      have i3c := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
      have i3s : (s - 1 : ℕ) + 1 = s := by omega
      have i3ss : M.slotStart S.C (s - 1) + 4 * Δ S = M.slotStart S.C s := by
        rw [i3sE, i3sE, ← i3s, Nat.mul_add, Nat.mul_one, i3s]
      have i3cs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
        have := i3c (s - 1); have := i3vT (s - 1); omega
      have i3cR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S = 4 * (Δ S : ℝ) * (s : ℝ) := by
        have h' : ((M.supportCutoff S.C (s - 1) + 2 * Δ S : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) := by
          rw [i3cs]
        rw [i3sE s] at h'; push_cast at h'; linarith
      have i3mx : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
      have i3m : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
        rcases le_total (2 * Δ S) Δs with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; push_cast; linarith
      rcases le_total (max (2 * Δ S) Δs) (M.supportCutoff S.C (s - 1)) with hle | hle
      · rw [Nat.cast_sub hle]; linarith
      · rw [Nat.sub_eq_zero_of_le hle]
        have hleR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast
        linarith
    · rw [max_eq_left h]
      exact htStart
  obtain ⟨hHeld, hBase, hUpd⟩ := (round_base_steps M F U) S A x R GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p φ φw ρp ρw E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hl hcl => hRoots k u c hl (le_trans hcl hcut₁)) hParent hOwner hs1
    hGST (hHonUpd s le_rfl (by omega)) (hHonTick s le_rfl (by omega)) (max tStart (duty_window_start S.C s)) htStart'
    (Activity.mem_activeThroughoutToTick_of_le (le_max_left tStart (duty_window_start S.C s)) hp) hHoldP
    (fun w hw => Activity.mem_activeThroughoutToTick_of_le hdwle (hHon s le_rfl (by omega) w hw)) hPropose
    hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf hShapeP hShapeW hFloorW
    hRootW (fun v hv => ancestorEq_trans (by rw [← (hShapeV v hv).1]; exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v) (hRootAr v hv))
    hHeadP
  -- step 2: the invariant through the round, from one slot's set to the next; the members of slot `s₂ + 1` read to
  -- their tick to its vote time inside their update reader of slot `s₂`
  obtain ⟨hInv, hVotes⟩ := (round_honestChainExtends_steps M F U) S A x R GST s s₂ Hon Hs B E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hl hcl => hRoots k u c hl (le_trans hcl hcut₂)) hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.sub_le s 1)))
    (by omega) hHonMono
    (by
      intro s' h1 h2 v hv'
      by_cases hs' : s' + 1 < s₂ + 2
      · exact hHon s' h1 hs' v hv'
      · have he : s' = s₂ + 1 := by omega
        subst he
        have hU := hHonUpd s₂ (by omega) (by omega) v (hHonMono s₂ (by omega) (by omega) hv')
        have hvt := hv (s₂ + 1)
        have hct := hc (s₂ + 1)
        have hdr := duty_window_start_real S (s₂ + 1)
        have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
          exact_mod_cast hsE (s₂ + 1)
        have hvR : ((M.voteTime S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hvt
        have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.voteTime S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hct
        push_cast at hsR hdr
        refine (mem_activeThroughoutToTick_of_le_end_int M x) R E (by omega) ?_ ?_ hU
        · linarith
        · linarith)
    (fun s' h1 h2 => hHonUpd s' h1 h2) (fun s' h1 h2 => hHonTick s' h1 h2) hHs
    hVoters hStep hStepLast hBase
  -- step 3: the attestations in `q`'s pool at its tick `kQ` to the start of slot `s''`, read from
  -- `tq := max (M.dutyWindowStart S.C s) GST`
  have hmxF1 := le_max_left (Δ_F S) Δs_F
  have hmxF2 := le_max_right (Δ_F S) Δs_F
  have hmxΔ := le_max_left (Δ S) Δs
  have hcm1 := hc (s - 1)
  have hvm1 := hv (s - 1)
  have hdws := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have hssE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔsF : Δs_F ≤ Δ_F S ∨ Δs_F + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
    rcases hΔs_F with h | h
    · left
      exact_mod_cast (show (Δs_F : ℝ) ≤ Δ_F S by linarith)
    · right
      exact_mod_cast (show ((Δs_F + 3 * Δ S : ℕ) : ℝ) ≤ ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have htqF : max (M.dutyWindowStart S.C s) GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C (s₂ + 2) := by
    rcases hdws with h | ⟨h, -⟩
    · have := le_max_left (M.dutyWindowStart S.C s) GST
      have := le_max_right (M.dutyWindowStart S.C s) GST
      rcases max_cases (M.dutyWindowStart S.C s) GST with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases max_cases (Δ_F S) Δs_F with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;> omega
    · rw [h, Nat.zero_max]
      exact hGSTF
  -- `q` ticks to the start of slot `s''` (its reader `hHonLast`)
  obtain ⟨kQ0, hkQ0, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonLast q hq)
  have hkQ : x.lbl (x.tickStep q (M.slotStart S.C (s₂ + 2))) = Event.tick q (M.slotStart S.C (s₂ + 2)) := by
    rw [(tickStep_eq_of_lbl M) x E hkQ0]
    exact hkQ0
  -- each member of `Q` ticks to the vote time of slot `s` before its tick to the support cutoff of slot `s + 1`,
  -- and keeps `B`
  have hBin : ∀ v ∈ Q, B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
    intro v hvQ
    obtain ⟨k1, hk1, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHon s le_rfl (by omega) v (hQ hvQ))
    obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v (hQ hvQ))
    have h12 := (tick_lt_of_clock_lt M) x E hk1 hk2 (by omega)
    have hB1 := hHeld v (hQ hvQ)
    unfold Trace.tickInput at hB1 ⊢
    rw [(tickStep_eq_of_lbl M) x E hk1] at hB1
    rw [(tickStep_eq_of_lbl M) x E hk2]
    exact ((grows_of_le M F) x R E v h12.le).1 hB1
  obtain ⟨hPool, hPoolT⟩ := (round_attestations_in_pool M F U) S A x R GST r s (M.slotStart S.C (s₂ + 2))
    (max (M.dutyWindowStart S.C s) GST) Q B q φv ρv E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy_F hs
    (by omega) ha hBslot
    (fun v hv' => hHonUpd s le_rfl (by omega) v (hQ hv'))
    (fun v hv' => hUpd v (hQ hv')) (fun v hv' => hBase.2.1 v (hQ hv'))
    (fun v hv' => hShapeV v (hQ hv')) (fun v hv' => hRootAr v (hQ hv'))
    hBin hLockBox
    (fun v hv' => hFloorV v (hQ hv')) hGSTF htqF
    (x.tickStep q (M.slotStart S.C (s₂ + 2))) hkQ hqWin
    (fun v hv' => hHoldF v (hQ hv'))
    hselq
  -- step 4: `q`'s proposal is on `B`'s chain
  have hss₂ : M.slotStart S.C (s₂ + 2) = M.slotStart S.C (s₂ + 1) + 4 * Δ S := hss (s₂ + 1)
  have hqUpd := hHonUpd s₂ (by omega) (by omega) q (hHonMono s₂ (by omega) (by omega) hq)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hqUpd
  have hRootsQ : RootsNameBlocksUntil M A x (x.time (x.tickStep q (M.supportCutoff S.C (s₂ + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkc]
    exact hRoots kc q _ hkc le_rfl
  -- the voters of slot `s₂ + 1` are active through the sync delay after Lemma 12's read time of slot `s₂ + 1`,
  -- inside their reader to the start of slot `s''`
  have hHoldQ : ∀ u ∈ Hs (s₂ + 1), u ∈ A.activeThroughout x
      ((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro u hu
    have huH := ((hHs (s₂ + 1) (by omega) (by omega)) u hu).1
    have hct := hc (s₂ + 1)
    have hvt := hv (s₂ + 1)
    have hst := hss (s₂ + 1)
    have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hsE (s₂ + 1)
    have hdr := duty_window_start_real S (s₂ + 1)
    have hle : max (2 * Δ S) Δs ≤ M.supportCutoff S.C (s₂ + 1) := by
      have := le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s - 1 ≤ s₂ + 1 by omega))
      have := le_max_right (Δ S) Δs
      rcases le_total (2 * Δ S) Δs with h2 | h2
      · rw [max_eq_right h2]; omega
      · rw [max_eq_left h2]; omega
    have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + 2 * Δ S := by
      exact_mod_cast (show M.supportCutoff S.C (s₂ + 1) = M.slotStart S.C (s₂ + 1) + 2 * Δ S by omega)
    have hs2R : ((M.slotStart S.C (s₂ + 2) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + 4 * Δ S := by
      exact_mod_cast hst
    have hΔsm : (Δs : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm2s
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHonLast u huH)
      (a' := M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs)
      (e := M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs + Δs)
      (by push_cast [Nat.cast_sub hle] at hdr hsR hm2R hΔsm hcR ⊢; linarith)
      (by push_cast [Nat.cast_sub hle] at hsR hm2R hΔsm hcR hs2R ⊢; linarith)
    rw [Nat.cast_add] at h
    exact h
  have hBB'p := (round_proposal_extends M F U) S A x R GST s₂ (Hon (s₂ + 1)) (Hs (s₂ + 1)) B B' q
    E hNet hSkew hRedeliver Sy hΔs hRootsQ hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s - 1 ≤ s₂ + 1 by omega)))
    ((honestChainExtends_mono M F) S A x (Hon s₂) (Hon (s₂ + 1)) B s₂
      (hHonMono s₂ (by omega) (by omega)) hInv) hVotes hq hqUpd
    (hHs (s₂ + 1) (by omega) (by omega)) hHoldQ
    hHonestQ
    hVotersQ hFrameQ hPropose'
  obtain ⟨i', hl', hsent'⟩ := id hPropose'
  obtain ⟨-, -, hB'par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s₂ + 1) i' B' q hl' hsent'
  have hB'p : B'.parent.AncestorEq B' := ancestorEq_of_parent? hB'par?
  have hBB' := ancestorEq_trans hBB'p hB'p
  -- step 5: the certificate
  have hd1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.1 hBB'p
  have hd2 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B'.parent B').2.2.2.1 hB'p
  by_cases heq : (M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h
  · have hT : (M.chainStateOf S.C B'.parent).T_h = (M.chainStateOf S.C B).T_h :=
      (((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.2 hBB'p heq.symm).symm
    have hPool' : ∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C (s₂ + 2))).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B'.parent).h ∧
        a.T = (M.chainStateOf S.C B'.parent).T_h.root := by
      rw [heq, hT]
      exact hPool
    obtain ⟨h53a, h53b⟩ := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E (s₂ + 2) q B'
      B'.parent Q hPropose' rfl hQuorum hPool'
    rw [heq, hT] at h53a h53b
    refine ⟨hBB', ?_, fun hFresh => ?_⟩
    · rcases h53a with h | h
      · exact Or.inl (by unfold Height at *; omega)
      · exact Or.inr h
    · obtain ⟨h1, h2⟩ := h53b (hPoolT hFresh)
      exact ⟨by unfold Height at *; omega, fun _ => h2⟩
  · have hlt : (M.chainStateOf S.C B).h < (M.chainStateOf S.C B'.parent).h := by
      unfold Height at *
      omega
    have hge : (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h := by
      unfold Height at *
      omega
    exact ⟨hBB', Or.inl hge, fun _ => ⟨hge, fun h => absurd h heq⟩⟩

/-- **Lemma 80, the height advances in a round, over frame shapes.** The proof: the instance of
`lem80wq_round_height_advances_steps` with one member set, the frames at the three reading points
read off the frame shapes over the window, the step conditions at the members' tick inputs and
`voterFrame_of_shape`, and `q`'s fork choice from `proposerFrame_of_shape`; the members hold `B`
before the vote time of slot `s` by `round_base_steps`. The audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`:
`lem80wq_round_height_advances_steps`, which the proof calls, reads them per tick.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: inside a window where every member's frame has one `head_height_floor` and a root on
`B`'s chain, the round's honest proposal is voted, confirmed and attested by every member, and the
next honest proposal, at a slot the round's attestations reach in time, is on its chain with the
height risen or the progress quorum on chain. -/
theorem lem80_round_height_advances_frame (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (φ : Height) (ρ : V → ℕ → Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart` (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
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
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hShape : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (ρ v j) φ)
    (hRootW : ∀ w ∈ Hon, (ρ w (x.tickStep w (M.voteTime S.C s))).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon, (ρ v (x.tickStep v (M.supportCutoff S.C (s + 1)))).AncestorEq B)
    (hRootAfter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (ρ v j).compatible B = true)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (ρ p (x.tickStep p (M.slotStart S.C s))).AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  classical
  -- the slots and the times
  have hR := S.C.R_ge_two
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast (slot_times M F U S s).2.2.2.2.2.1
  have hsE : ∀ k, M.slotStart S.C k = 4 * Δ S * k :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hss : ∀ k, M.slotStart S.C (k + 1) = M.slotStart S.C k + 4 * Δ S := fun k => by
    rw [hsE, hsE, Nat.mul_add, Nat.mul_one]
  have hvT : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hf : ∀ k, M.viewFreeze S.C k = M.slotStart S.C k + 3 * Δ S := fun k => (slot_times M F U S k).2.2.1
  have hsR : ∀ k, ((M.slotStart S.C k : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (k : ℝ) := fun k => by
    rw [hsE k]; push_cast; ring
  have hmx : (Δ S : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
    have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith
  have hmxs : (Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
    have := le_max_right (Δ S : ℝ) (Δs : ℝ); linarith
  have hsm : s - 1 + 1 = s := by omega
  have hst1 : 0 < M.slotStart S.C s := by rw [hsE s]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hΔ) hs1
  -- a slot start before `s''` is at least `4Δ` before the start of slot `s''`
  have hstle : ∀ s₁, s₁ + 1 ≤ s'' → M.slotStart S.C s₁ + 4 * Δ S ≤ M.slotStart S.C s'' := fun s₁ h => by
    rw [← hss s₁]; exact (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S h
  have hstm : ∀ s₁ s₂, s₁ ≤ s₂ → M.slotStart S.C s₁ ≤ M.slotStart S.C s₂ := fun s₁ s₂ h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S h
  have hsubR : ∀ n m : ℕ, m ≤ n → ((n - m : ℕ) : ℝ) = (n : ℝ) - m := fun n m h => Nat.cast_sub h
  have hmxle : max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1) := by omega
  have hcs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
    have := hss (s - 1); rw [hsm] at this; have := hc (s - 1); have := hvT (s - 1); omega
  have hdwR := duty_window_start_real S s
  -- the duty window's start (the protocol's integer) grows with the slot
  have hdwM : ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → duty_window_start S.C s₁ ≤ duty_window_start S.C s₂ := by
    intro s₁ s₂ h
    have h1 := duty_window_start_real S s₁
    have h2 := duty_window_start_real S s₂
    have hR' : (s₁ : ℝ) ≤ s₂ := by exact_mod_cast h
    have hD : (0 : ℝ) ≤ Δ S := by positivity
    have : ((duty_window_start S.C s₁ : ℤ) : ℝ) ≤ ((duty_window_start S.C s₂ : ℤ) : ℝ) := by
      rw [h1, h2]; nlinarith
    exact_mod_cast this
  -- every member's reader, ended at a tick to a clock value `b'` from the start of slot `s` to `Δ` before the start of
  -- slot `s''`
  have hRd : ∀ v ∈ Hon, ∀ b' : ℕ, M.slotStart S.C s ≤ b' → b' + Δ S ≤ M.slotStart S.C s'' →
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) b' := by
    intro v hv b' h2 h3
    have h2R : ((M.slotStart S.C s : ℕ) : ℝ) ≤ (b' : ℝ) := by exact_mod_cast h2
    have h3R : (b' : ℝ) + Δ S ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by exact_mod_cast h3
    have hsRs := hsR s
    refine (mem_activeThroughoutToTick_of_le_end_int M x) R E (by omega) ?_ ?_ (hHon v hv)
    · rw [hdwR]; linarith
    · linarith
  have hTk : ∀ v ∈ Hon, ∀ c : ℕ, M.slotStart S.C s ≤ c → c + Δ S ≤ M.slotStart S.C s'' →
      x.lbl (x.tickStep v c) = Event.tick v c := by
    intro v hv c h2 h3
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hRd v hv c h2 h3)
    rw [(tickStep_eq_of_lbl M) x E hk]; exact hk
  have hTkE : ∀ v ∈ Hon, x.lbl (x.tickStep v (M.slotStart S.C s'')) = Event.tick v (M.slotStart S.C s'') := by
    intro v hv
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHon v hv)
    rw [(tickStep_eq_of_lbl M) x E hk]; exact hk
  have hlt : ∀ (v : V) (c c' : ℕ), x.lbl (x.tickStep v c) = Event.tick v c →
      x.lbl (x.tickStep v c') = Event.tick v c' → c < c' → x.tickStep v c < x.tickStep v c' :=
    fun v c c' h h' hcc => (tick_lt_of_clock_lt M) x E h h' hcc
  have hle : ∀ (v : V) (c c' : ℕ), x.lbl (x.tickStep v c) = Event.tick v c →
      x.lbl (x.tickStep v c') = Event.tick v c' → c ≤ c' → x.tickStep v c ≤ x.tickStep v c' := by
    intro v c c' h h' hcc
    rcases Nat.lt_or_eq_of_le hcc with hcc | hcc
    · exact (hlt v c c' h h' hcc).le
    · rw [hcc]
  -- the ticks of slot `s` every member reads at, inside the window
  have hvs := hvT s
  have hcs1 := hc (s + 1)
  have hvs1 := hvT (s + 1)
  have hss1 := hss s
  have hst2 := hstle (s + 1) (by omega)
  have hss2 := hss (s + 1)
  have hTs : ∀ v ∈ Hon, x.lbl (x.tickStep v (M.slotStart S.C s)) = Event.tick v (M.slotStart S.C s) :=
    fun v hv => hTk v hv _ le_rfl (by omega)
  have hTv : ∀ v ∈ Hon, x.lbl (x.tickStep v (M.voteTime S.C s)) = Event.tick v (M.voteTime S.C s) :=
    fun v hv => hTk v hv _ (by omega) (by omega)
  have hTc : ∀ v ∈ Hon, x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) =
      Event.tick v (M.supportCutoff S.C (s + 1)) := fun v hv => hTk v hv _ (by omega) (by omega)
  have hsv : ∀ v ∈ Hon, x.tickStep v (M.slotStart S.C s) ≤ x.tickStep v (M.voteTime S.C s) :=
    fun v hv => hle v _ _ (hTs v hv) (hTv v hv) (by omega)
  have hvE : ∀ v ∈ Hon, x.tickStep v (M.voteTime S.C s) < x.tickStep v (M.slotStart S.C s'') :=
    fun v hv => hlt v _ _ (hTv v hv) (hTkE v hv) (by omega)
  have hsc : ∀ v ∈ Hon, x.tickStep v (M.slotStart S.C s) ≤ x.tickStep v (M.supportCutoff S.C (s + 1)) :=
    fun v hv => hle v _ _ (hTs v hv) (hTc v hv) (by omega)
  have hcE : ∀ v ∈ Hon, x.tickStep v (M.supportCutoff S.C (s + 1)) ≤ x.tickStep v (M.slotStart S.C s'') :=
    fun v hv => hle v _ _ (hTc v hv) (hTkE v hv) (by omega)
  have hsE' : ∀ v ∈ Hon, x.tickStep v (M.slotStart S.C s) ≤ x.tickStep v (M.slotStart S.C s'') :=
    fun v hv => le_trans (hsv v hv) (hvE v hv).le
  -- the frame shapes at the three reading points of slot `s`
  have hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) (ρ p (x.tickStep p (M.slotStart S.C s))) φ :=
    hShape p hp _ le_rfl (hsE' p hp)
  have hShapeW : ∀ w ∈ Hon, FrameShape M (x.tickInput w (M.voteTime S.C s)) (ρ w (x.tickStep w (M.voteTime S.C s))) φ :=
    fun w hw => hShape w hw _ (hsv w hw) (hvE w hw).le
  have hShapeV : ∀ v ∈ Hon, FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1)))
      (ρ v (x.tickStep v (M.supportCutoff S.C (s + 1)))) φ :=
    fun v hv => hShape v hv _ (hsc v hv) (hcE v hv)
  -- `p`'s `head_height_floor` before the start of slot `s` is at most the heights of `B`'s parent and of `B`
  have hPropose₀ : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    rw [hsm]; exact hPropose
  have hParentIn₀ : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s - 1 + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s - 1 + 1)))).tree := by
    rw [hsm]; exact hParentIn
  have hφ : φ ≤ (M.chainStateOf S.C B.parent).h := by
    have h := (proposal_parent_viable M F U) S A x R E (s - 1) B p hPropose₀ hParentIn₀
    rw [hsm, hShapeP.2] at h
    exact h
  have hBHeight : φ ≤ (M.chainStateOf S.C B).h := by
    have h := (proposal_viable M F U) S A x R E (s - 1) B p hPropose₀ hParentIn₀
    rw [hsm, hShapeP.2] at h
    exact h
  -- the members' rows of Lemma 80, from their readers `hHon`
  have hHonR : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon,
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s') := by
    intro s' h1 h2 v hv
    have := hstm s s' h1
    have := hstle s' (by omega)
    have := hvT s'
    exact Activity.mem_activeThroughoutToTick_of_le (hdwM s s' h1) (hRd v hv _ (by omega) (by omega))
  have hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon, v ∈ updaterAt M S A x s' := by
    intro s' h1 h2 v hv
    have := hstm s (s' + 1) (by omega)
    have := hstle (s' + 1) (by omega)
    have := hvT (s' + 1)
    have := hc (s' + 1)
    exact Activity.mem_activeThroughoutToTick_of_le (hdwM s (s' + 1) (by omega)) (hRd v hv _ (by omega) (by omega))
  have hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) := by
    intro s' h1 h2 u hu hmem
    obtain ⟨k, w, hk, -, huk⟩ := (Finset.mem_filter.1 hmem).2
    have htk := (E.tick_active k w _ hk).2.2
    have h3 := hstle (s' + 1) (by omega)
    have h4 := hc (s' + 1)
    have h5 := hvT (s' + 1)
    have h6R : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s' + 1) + Δ S ≤ M.slotStart S.C s'' by omega)
    exact (not_mem_corruptedAtTime_of_mem_activeThroughoutToTick M F) x R E (hHon u hu) (t := x.time k)
      (by linarith) (Activity.mem_corruptedAtTime.2 ⟨k, le_rfl, huk⟩)
  -- the holder rows of the members and of the proposer, inside their readers
  have hHoldV : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro w hw
    have hfs := hf s
    have hle' : max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
    have hfR : ((M.viewFreeze S.C s : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) + 3 * Δ S := by exact_mod_cast hfs
    have hmR : (Δs : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_right (Δ S) Δs
    have hmR' : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := by push_cast; rfl
    have hsRs := hsR s
    have h8 : ((M.slotStart S.C s : ℕ) : ℝ) + 8 * Δ S ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
      have := hstle (s + 1) (by omega); exact_mod_cast (show M.slotStart S.C s + 8 * Δ S ≤ M.slotStart S.C s'' by omega)
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHon w hw)
      (a' := M.viewFreeze S.C s - max (Δ S) Δs) (e := M.viewFreeze S.C s - max (Δ S) Δs + Δs)
      (by rw [hsubR _ _ hle', hdwR]; linarith) (by push_cast [hsubR _ _ hle']; linarith)
    rw [Nat.cast_add] at h
    exact h
  have hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have hle' : max (Δ S) Δs ≤ M.slotStart S.C s := by omega
    have hmR : (Δs : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_right (Δ S) Δs
    have hmR' : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := by push_cast; rfl
    have hsRs := hsR s
    have h8 : ((M.slotStart S.C s : ℕ) : ℝ) + 8 * Δ S ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
      have := hstle (s + 1) (by omega); exact_mod_cast (show M.slotStart S.C s + 8 * Δ S ≤ M.slotStart S.C s'' by omega)
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHon p hp)
      (a' := M.slotStart S.C s - max (Δ S) Δs) (e := M.slotStart S.C s - max (Δ S) Δs + Δs)
      (by rw [hsubR _ _ hle', hdwR]; linarith) (by push_cast [hsubR _ _ hle']; linarith)
    rw [Nat.cast_add] at h
    exact h
  -- the roots name blocks at every tick to a clock value at most the support cutoff of slot `s'' − 1`
  have hRootsT : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k) := by
    exact hRoots
  have hcut₁ : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s'' - 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- step 1: every member holds `B` at its tick to the vote time of slot `s` (the base of the round), with the reader
  -- start `max tStart (duty_window_start S.C s)`
  have hdwle : duty_window_start S.C s ≤ max tStart (duty_window_start S.C s) := le_max_right _ _
  have htStart' : ((max tStart (duty_window_start S.C s) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total tStart (duty_window_start S.C s) with h | h
    · -- the duty window's start `st(s) + Δ − 4Δk` is more than both clock bounds before Lemma 12's read time of
      -- slot `s − 1`, truncated at `0` or not
      rw [max_eq_right h, duty_window_start_real S s]
      have i3A := E.ahead_nonneg
      have i3B := E.behind_nonneg
      have i3D : (0 : ℝ) ≤ Δ S := by positivity
      have i3k8 : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast (slot_times M F U S s).2.2.2.2.2.1
      have i3sE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
      have i3vT := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
      have i3c := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
      have i3s : (s - 1 : ℕ) + 1 = s := by omega
      have i3ss : M.slotStart S.C (s - 1) + 4 * Δ S = M.slotStart S.C s := by
        rw [i3sE, i3sE, ← i3s, Nat.mul_add, Nat.mul_one, i3s]
      have i3cs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
        have := i3c (s - 1); have := i3vT (s - 1); omega
      have i3cR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S = 4 * (Δ S : ℝ) * (s : ℝ) := by
        have h' : ((M.supportCutoff S.C (s - 1) + 2 * Δ S : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) := by
          rw [i3cs]
        rw [i3sE s] at h'; push_cast at h'; linarith
      have i3mx : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
      have i3m : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
        rcases le_total (2 * Δ S) Δs with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; push_cast; linarith
      rcases le_total (max (2 * Δ S) Δs) (M.supportCutoff S.C (s - 1)) with hle | hle
      · rw [Nat.cast_sub hle]; linarith
      · rw [Nat.sub_eq_zero_of_le hle]
        have hleR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast
        linarith
    · rw [max_eq_left h]
      exact htStart
  obtain ⟨hHeld, -, -⟩ := (round_base_steps M F U) S A x R GST s Hon (Hs s) (Hs (s - 1)) H X
    B p φ (fun _ => φ) (ρ p (x.tickStep p (M.slotStart S.C s)))
    (fun w => ρ w (x.tickStep w (M.voteTime S.C s)))
    E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hl hcl => hRootsT k u c hl (le_trans hcl hcut₁)) hParent hOwner hs1
    hGST (hHonUpd s le_rfl (by omega)) (hHonTick s le_rfl (by omega)) (max tStart (duty_window_start S.C s)) htStart'
    (Activity.mem_activeThroughoutToTick_of_le (le_max_left tStart (duty_window_start S.C s)) hpR)
    hHoldP
    (fun w hw => Activity.mem_activeThroughoutToTick_of_le hdwle (hHonR s le_rfl (by omega) w hw)) hPropose
    hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf hShapeP hShapeW (fun _ _ => ⟨le_rfl, hφ⟩)
    hRootW (fun v hv => ancestorEq_trans (by rw [← (hShapeV v hv).1]; exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v) (hRootAr v hv))
    hHeadP
  -- the frame of `q` at its tick to the start of slot `s''`
  have hFrameQ := (proposerFrame_of_shape_st M F) S A x R E (x.tickStep q (M.slotStart S.C s'')) q B
    (ρ q (x.tickStep q (M.slotStart S.C s''))) φ (hShape q hq _ (hsE' q hq) le_rfl)
    (hRootAfter q hq _ (hvE q hq) le_rfl)
    (((grows_of_le M F) x R E q (hvE q hq).le).1 (hHeld q hq)) hBHeight
  -- the step conditions after the action time, from the frame shapes
  have hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon, StepFrameAt M S A x B s' w := by
    intro s' h1 h2 w hw
    have hVF := (voterFrame_of_shape M F U) S A x R s s'' s' w B φ (ρ w) E hSkew h1 (by omega) (hHon w hw)
      (hShape w hw) (hRootAfter w hw) (hHeld w hw) hBHeight
    refine ⟨hVF.1, hVF.2, ?_⟩
    -- the finalized block at the tick to the support cutoff of slot `s' + 2` is an ancestor of the root there
    have h3 := hstle (s' + 2) (by omega)
    have h4 := hc (s' + 2)
    have h5 := hvT (s' + 2)
    have h6 := hstm s (s' + 2) (by omega)
    have hT := hTk w hw (M.supportCutoff S.C (s' + 2)) (by omega) (by omega)
    have hj1 : x.tickStep w (M.voteTime S.C s) < x.tickStep w (M.supportCutoff S.C (s' + 2)) :=
      hlt w _ _ (hTv w hw) hT (by omega)
    have hj2 : x.tickStep w (M.supportCutoff S.C (s' + 2)) ≤ x.tickStep w (M.slotStart S.C s'') :=
      hle w _ _ hT (hTkE w hw) (by omega)
    have hSh := hShape w hw _ (le_trans (hsv w hw) hj1.le) hj2
    have hFr := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E
      (x.tickStep w (M.supportCutoff S.C (s' + 2))) w
    rw [hSh.1] at hFr
    exact _root_.GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hFr (hRootAfter w hw _ hj1 hj2)
  exact (lem80wq_round_height_advances_steps M F U Fx) S A x R GST r s s'' (fun _ => Hon) Q Hs H X B B' p q
    φ (fun _ => φ) (fun _ => φ) (ρ p (x.tickStep p (M.slotStart S.C s)))
    (fun w => ρ w (x.tickStep w (M.voteTime S.C s))) (fun v => ρ v (x.tickStep v (M.supportCutoff S.C (s + 1))))
    E hNet hSkew hRedeliver hRootsT hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    (fun _ _ _ => Finset.Subset.refl Hon) hHonR hHonUpd hHonTick
    (fun v hv => Activity.mem_activeThroughoutToTick_of_le (hdwM s (s'' - 1) (by omega)) (hHon v hv))
    hHonestQ hHold42 hHoldV hHoldF tStart htStart hpR hHoldP hPropose hHsPrev hHold
    hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    hShapeP hShapeW hShapeV (fun _ _ => ⟨le_rfl, hφ⟩) (fun _ _ => hBHeight) hRootW hRootAr hHeadP hStep
    (fun w hw => by
      have h := (voterFrame_of_shape M F U) S A x R s s'' (s'' - 2) w B φ (ρ w) E hSkew (by omega)
        (by omega) (hHon w hw) (hShape w hw) (hRootAfter w hw) (hHeld w hw) hBHeight
      rw [show s'' - 2 + 1 = s'' - 1 by omega] at h
      exact h)
    hQ hQuorum hLockBox hselq hq hqWin hFrameQ hPropose'

end GoldilocksCorrectness.Record.Proofs.Executions

