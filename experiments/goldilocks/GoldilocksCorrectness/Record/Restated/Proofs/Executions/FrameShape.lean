module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ComposedProposalVoteStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FrameStatementsFGState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Statements.Executions.ComposedProposalVoteStatements
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# FrameShape, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/FrameShape.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 59, 60 and 61, the vote, the
confirmation and the attestation over a frame shape. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor CountedVotes FrameShape VoterTreeAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ancestorEq_refl compatible_iff
  ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Under a frame shape with root `ρ` and `head_height_floor` (the least chain-state height a viable block may have) equal to `φ` at `v`'s state before the time `t`, a block of
`v`'s tree that `ρ` is an ancestor of, whose chain-state height is at least `φ`, is in `v`'s viable
tree: the finalized block is the root or an ancestor of it (Lemma 46), and the block's chain state
is its own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `B`: the block; `ρ`: the root; `φ`: the value of `head_height_floor`.

Read aloud: a block of `v`'s tree before `t` whose ancestor or equal is the root `ρ` of a frame
shape at that node state, and whose chain-state height is at least the shape's height `φ`, is in
`v`'s viable tree. -/
theorem mem_viable_tree_of_frameShape_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (B ρ : Block V) (φ : Height)
    (hShape : FrameShape M (x.stateBefore t v) ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore t v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore t v))
      (M.fg_to_ac (x.stateBefore t v)).tree := by
  refine (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_of_frameShape_of_core M F) S.C S.P S.X _
    (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) v).1 ρ φ B hShape ?_ hRootV hBin hBHeight
  rw [← hShape.1]
  exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E t v

/-- Lemma 59, the next slot's honest vote names the honest proposal, over a frame shape. The proof;
the audited statement is in `Statements/Executions/FrameShapeStatements.lean`.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and Lemma 24, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the two frames have roots `ρ_p`, `ρ_w` and one `head_height_floor` value `φ`; some accepted block of `p` on
`ρ_p`'s chain descending from `X` reaches `head_height_floor`; `w`'s root is on `B`'s chain; and `B` reaches
`head_height_floor` — then `w`'s vote names `B`. -/
theorem lem59_goldfish_vote_names_honest_proposal_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) ρ_p φ)
    (hShapeW : FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    (hRootW : ρ_w.AncestorEq B)
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h) :
    vote.head = B.root := by
  -- the two ticks, and the honesty Lemma 11 reads there
  obtain ⟨kW, hkW, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  obtain ⟨i, hl, hsent⟩ := id hPropose
  have hpT : p ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact E.not_mem_corrupted_of_tick hl
  have hwT : w ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkW]
    exact E.not_mem_corrupted_of_tick hkW
  -- Lemma 56 at the two shapes (at the node invariant of each tick input)
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) :=
    (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p hpT).1
  have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) :=
    (lem11_node_invariant M F S A x R E (x.tickStep w (M.voteTime S.C (s + 1))) w hwT).1
  obtain ⟨hRp, -, hHp⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F)
    S.C S.P S.X _ hInvP _ _ hShapeP
  obtain ⟨hRw, hVw, -⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F)
    S.C S.P S.X _ hInvW _ _ hShapeW
  -- Lemma 46: each finalized block is its fork-choice root or an ancestor of it
  have hFρp : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq ρ_p := by
    rw [← hShapeP.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ p
  have hFρw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq ρ_w := by
    rw [← hShapeW.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ w
  have hF2p : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root := by
    rw [hRp]
    exact hFρp
  have hF2w : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B := by
    rw [hRw]
    exact hRootW
  -- a viable head of `p`'s frame that is `X` or a descendant of `X`
  have hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W := by
    obtain ⟨W, hW, hXW, hρW, hφW⟩ := hHeadP
    have hFW := ancestorEq_trans hFρp hρW
    exact ⟨W, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW, hFW⟩,
      (hHp W).2 ⟨hW, hFW, hρW, hφW⟩, hXW⟩
  -- `w` holds `B` at its tick input: steps 1 to 3 of Lemma 24's proof
  obtain ⟨-, -, hBpar?, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentHeld : B.parent ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree := by
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).1
    · obtain ⟨W, hW, -, hXW⟩ := hF3p
      refine (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p W B.parent (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hW).1 ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans hF2p
        ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _)
  have hBp : B ∈ (x.st (i + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R s i B p
      E hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B :=
    ancestorEq_trans hFρw hRootW
  -- `w`'s step form from more than both clock bounds before the start of slot `s + 1`, from its reader
  have hwR := (tick_window_ahead_of_activeThroughoutToTick_int M x R E hw (c := M.slotStart S.C (s + 1)) (by
    have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_le_slotStart_succ M.toSlotLayout F.sched) S s
    have h1 : ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C (s + 1) : ℝ) := by
      exact_mod_cast (Nat.sub_le _ _).trans hc
    linarith))
  have hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem22_proposal_held_by_voter M F U) S A x R GST s i B p
      w E hNet hSkew hRedeliver hRoots hParent
      (by have := le_max_left (Δ S) Δs
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
          omega) hwR hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- `B` passes `w`'s viability test, and the two `head_height_floor` values are `φ`
  have hBViable : M.is_viable (x.tickInput w (M.voteTime S.C (s + 1))) B = true :=
    (hVw B hBw).2 hBHeight
  have hFloor : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) =
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1))) :=
    hShapeP.2.trans hShapeW.2.symm
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem24_goldfish_vote_names_honest_proposal_composed M F U)
    S A x R GST s Hs H X B p w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs
    hVoters hHold tStart htStart hp hHoldP hw hPropose hSend hOnly hRootNew hF3p hApX hF2w hLocksW hBViable hFloor

/-- Lemma 60, the confirmation update makes a voter-majority block fast and locks it, over a root.
The proof; the audited statement is in `Statements/Executions/FrameShapeStatements.lean`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: Lemma 29, which the proof calls, takes blocks as
held up to the support cutoff of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the root of `v`'s fork choice is `B` or an ancestor of `B`, Lemma 29's conclusion
holds. -/
theorem lem60_update_confirmation_fast_locks_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hRootV : (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq B) :
    B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) := by
  -- Lemma 29, with the finalized block at the tick input an ancestor of its fork-choice root
  exact (lem29_update_confirmation_fast_locks_voter_majority_block M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold
    hVoters hHalf hBne hv
    (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v)
      hRootV)

/-- The hypotheses of Lemma 55 on the viable tree and the record, from a frame shape at `v`. The
proof; the audited statement is in `Statements/Executions/FrameShapeStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the frame at `v` has its root on `B`'s chain and its `head_height_floor` at most `B`'s height, and `v`
holds no lock at `B`'s height on another block — then Lemma 55's viable-tree and record hypotheses
hold. -/
theorem lem61_frame_hypotheses (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    (hShape : FrameShape M (x.stateBefore (M.supportCutoff S.C (s + 1)) v) ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).tree)
    (hLockBox : (x.stateBefore (M.supportCutoff S.C (s + 1)) v).justifiedHeight <
        (M.chainStateOf S.C B).h ∨
      (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
        (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).tree ∧
      ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) := by
  refine ⟨(mem_viable_tree_of_frameShape_of_stateBefore M F) S A x R E _ v B ρ φ hShape hRootV hBHeight
    hBin, ?_⟩
  rcases hLockBox with hlt | hnone | hlock
  · exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.lock_none_of_h_j_lt_of_stateBefore M F) S A x R E _ v _ hlt)
  · exact Or.inl hnone
  · exact Or.inr ⟨hlock, (GoldilocksCorrectness.Record.Statements.Executions.lockNamesSent_of_stateBefore M F) S A x R E _ v _ _ hlock⟩

/-- Lemma 61, every honest validator with the honest proposal as its source attests for its
height, over a frame shape. The proof; the audited statement is in
`Statements/Executions/FrameShapeStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the frame at `v` has root `ρ`, on `B`'s chain, and `head_height_floor` at most `B`'s height; the cache
`h_j` is less than `B`'s height, or there is no lock at that height, or the lock there is `B`'s
`T_h` — then Lemma 55's conclusion. -/
theorem lem61_honest_validator_attests_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs : s = r * S.C.R)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (hSaved : M.savedConfirmation n' s = some B)
    (hFast : B ∈ M.fastBlocks n')
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hShape : FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree)
    (hLockBox : (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight <
        (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) :
    (∃ (i : ℕ) (a : Attestation V),
      x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = v ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h = (M.chainStateOf S.C B).h ∧ b.T = (M.chainStateOf S.C B).T_h.root) := by
  -- Lemma 55's viable-tree and record hypotheses at `v`'s tick input, `x.st (x.tickStep v c) v`
  have hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_of_frameShape_of_core M F) S.C S.P S.X _
      (lem11_node_invariantCore_of_run M F S x R (x.tickStep v (M.supportCutoff S.C (s + 1))) v).1 ρ φ B hShape ?_
      hRootV hBin hBHeight
    rw [← hShape.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v
  have hRecord : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      ((x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
          some (M.chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
          b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root) := by
    rcases hLockBox with hlt | hnone | hlock
    · exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.lock_none_of_h_j_lt_of_exec M F) S A x R E _ v _ hlt)
    · exact Or.inl hnone
    · exact Or.inr ⟨hlock, (GoldilocksCorrectness.Record.Statements.Executions.lockNamesSent_of_exec M F) S A x R E _ v _ _
        hlock⟩
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem55_honest_validator_attests_for_height M F U) S
    A x R r s B v E hs hv n' sent hUpdate hAwake hSaved hFast hLocks hViable hRecord

end GoldilocksCorrectness.Record.Proofs.Executions

