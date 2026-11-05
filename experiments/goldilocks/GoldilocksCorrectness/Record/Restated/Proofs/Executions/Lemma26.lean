module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameForkChoice
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFactsViableTree
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Statements.Routines.WalkEndStatements
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Proofs.Routines.WalkEndMerge
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma26, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma26.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 26, an honest Goldfish vote extends the
block a voter majority's votes extend, with the votes held and as stated. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem voteTime_eq
  voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes AwakeFor AnchorAt VoterTree
  VoterTreeAt)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible
  occurrenceBefore_eq_true_iff)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  mem_voter_block_tree_iff tau_eq_some_blockStamp occurrenceBefore_eq_true_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Lemma 26b, the next slot's honest Goldfish vote names a block the voter holds, on the chain
of a block a voter majority voted for. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean`.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the Goldfish vote `w` sends at the vote time of slot `s + 1` is for a block `H_w` that
`w` holds and that is `R` or a descendant of `R`, when the honest voters of `Hs`, who voted for `R`
or descendants of `R`, are more than half of the voters `w` counts. -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (R : Block V) (w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    -- the block of every lock entry live at `t₃` that `w`'s revocation leaves is compatible
    -- with `R`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ R.AncestorEq H_w := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  -- the times; the slot of `t₃`, read by the spec's clock (the model's slot of a natural-number
  -- time is the spec's, `U`)
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hslot₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hfreeze : ∀ a d : Int, 0 < d → a + 2 * d < a + 3 * d := by
    intro a d hd
    omega
  have h23 : ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
    WithBot.coe_lt_coe.2 (hfreeze _ _ S.C.Δ_pos)
  -- step 1: the run: `w`'s vote entered the sent log at the step `i`, `w`'s tick to `t₃`, which
  -- answered the outcome `(n', sent)` holding the vote
  obtain ⟨i, hl, hm⟩ := hSend
  obtain ⟨hwact, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F Run E) hl hm
  have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hRootsΦ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x Run E i w
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x Run E i w hwi).1
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x Run E i w
  -- step 2: the walk (Lemma 14 over the record, the field `tick_vote_head` of `F.tk3`, from the
  -- tick's input state; the tick ran from `w`'s state before `t₃`, awake for the slot): `w`'s vote
  -- is for the end `H_w` of the walk through the viable part of `w`'s voter's tree (`VoterTree`),
  -- from the anchor over `w`'s frame with the lock entries the tick left (`AnchorAt`)
  obtain ⟨-, hvi, hvs, -, ⟨τw, hτw, hτwle⟩, H_w, ⟨votes, support_votes, hCounted, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote hrun hInvT hvote
  rw [hslot₃] at hτwle hvs
  have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) := ⟨τw, hτw, hτwle⟩
  have hrun' := hrun
  rw [hslot₃] at hCounted hWalk
  rw [Nat.add_sub_cancel] at hWalk
  have hInvW := hInvT
  -- the vote is `w`'s slot-`(s + 1)` vote for `H_w` (the validator of the tick's input state is
  -- `w`, Lemma 11)
  rw [hti, (lem11_node_invariant M F S A x Run E i w hwi).2.1] at hvi
  have hvote' : vote = GoldfishVote.mk w (s + 1) H_w.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable
  -- tree
  have hHwT : H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
    have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, D ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
      fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInvW]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvW
        · exact F.nd.nodeInv_finalized_mem_tree hInvW
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) H_w).1 h1).1
  -- the anchor is a descendant of the fgroot (or the fgroot)
  have hRAw : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)) := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | h
    · rw [h]
      exact ancestorEq_refl _
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
  -- the case `R` an ancestor of `w`'s finalized block: the walk's end is the anchor or a
  -- descendant of it, the anchor is the fgroot or a descendant of it, and the fgroot is `w`'s
  -- finalized block or a descendant of it
  rcases (compatible_iff _ _).1 (compatible_of_ancestorEq_compatible hFroot hF2) with hFR | hRF
  swap
  · have hAH : (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).AncestorEq H_w := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1
    exact ⟨H_w, hHwT, hvote', ancestorEq_trans hRF (ancestorEq_trans hFroot (ancestorEq_trans hRAw hAH))⟩
  -- the case `w`'s finalized block an ancestor of `R`, hence of every `H u`
  have hF1 : ∀ u ∈ Hs, (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq (H u) :=
    fun u hu => ancestorEq_trans hFR (hHs u hu).2.2.2.2
  have hVb : M.voters_count votes < 2 * Hs.card := hVoters votes support_votes hCounted
  have hCv := hCounted.1
  have hCs := hCounted.2
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- step 3: the delivered votes
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) s (H u) u :=
    (lem12_honest_vote_delivered_until_of_steps M F U) S A x Run GST s (M.voteTime S.C (s + 1)) Hs H w
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST
      (by
        have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
        omega) i hl
      (fun u hu => ⟨(hHs u hu).1, (tickStep_eq_of_lbl M) x E hl ▸ (hHs u hu).2.1, (hHs u hu).2.2.1,
        (hHs u hu).2.2.2.1⟩)
      hHold hw hF1
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 4: the locks: the block of every lock entry the tick at `t₃` left, live at `t₃`, is
  -- compatible with `R`
  have hLocksLive := hLocks n' sent hrun' hAwake
  -- step 5: the anchor is compatible with `R`: it is the fgroot (compatible with `R` by F2), or an
  -- ancestor of the block of a live lock entry the tick left
  have hAnchor : (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).compatible R = true := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases_locked M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | ⟨-, e, he, hd, heT, hAe⟩
    · rw [h]
      exact hF2
    · have hlive : M.is_live (x.tickInput w (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true := by
        simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
        exact ⟨hd, heT⟩
      exact compatible_of_ancestorEq_compatible hAe (hLocksLive e he hlive)
  -- step 6: the start: when `R` is the fgroot or an ancestor of it, the anchor is a descendant of
  -- the fgroot; otherwise Lemma 7 with F3's viable head, every block after the anchor up to `R`
  -- being in the voter's tree: it is in `w`'s tree as an ancestor of `H u₀`, has `w`'s finalized
  -- block as an ancestor through the fgroot and the anchor, and is stamped no later than `H u₀`,
  -- which is stamped no later than the resolution of `u₀`'s vote, strictly before
  -- `S.C.t_ s + 2 · S.C.Δ`, hence before the view freeze `S.C.t_ s + 3 · S.C.Δ`
  have hStart : StartsTowards (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)) R (M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1))) := by
    rcases (compatible_iff _ _).1 hF2 with hRoot | hRoot
    · obtain ⟨W, hW, hWv, hRW⟩ := hF3 hRoot
      refine (GoldilocksCorrectness.Record.Statements.Routines.lem7_startsTowards_of_compatible M F) _ _ _ R W hAnchor hRAw ?_
        ⟨(GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) W).2 hW, hWv⟩ hRW
      intro P hXP _ hPR
      obtain ⟨-, -, hHΦ, ⟨y, hy, hyb⟩, -⟩ := hHeld u₀ hu₀
      have hHT : H u₀ ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).1
      have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPR (hHs u₀ hu₀).2.2.2.2
      have hPT : P ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x Run E _ w _ P hHT hPH
      have hFP : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq P :=
        ancestorEq_trans hFroot (ancestorEq_trans hRAw hXP)
      have hPΦ : P ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hPT, hFP⟩
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := (ancestor_blockStamp_le M F) S A x Run E _ w (H u₀) P hHT hPH
      -- the resolution of `u₀`'s vote is the later of its stamp and its head block's
      obtain ⟨τv, τH', H', -, hH'Φ, hroot, -, hτH', hy'⟩ := hy
      have hH' : H' = H u₀ := hRootsΦ H' hH'Φ (H u₀) hHΦ hroot
      rw [hH'] at hτH'
      have hτHH' : τH = τH' := Option.some_injective _ (hτH.symm.trans hτH')
      obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
      have hyy : y = y' := Option.some_injective _ hyy'
      have hτle : τH' ≤ y := by rw [hy']; exact le_max_right _ _
      have hτlt : τP < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
        lt_of_le_of_lt hle (hτHH' ▸ lt_of_le_of_lt hτle (hyy ▸ lt_trans hy'lt h23))
      refine (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) P).2 ⟨hPΦ, τP, hτP, Or.inl ?_⟩
      rw [Nat.add_sub_cancel]
      exact hτlt
    · exact Or.inl (ancestorEq_trans hRoot hRAw)
  -- step 7: the walk: Lemma 2 over the walk predicate with `Sup := Hs`, every support vote being
  -- counted (an included support vote is one of its block's votes, the block well formed by the
  -- node invariant), each `u ∈ Hs` voting once among the counted votes (a counted pool vote by
  -- `HeldEarlyVoteFor`'s uniqueness, a counted included vote by `included_vote_eq_of_owner`), and
  -- `hVoters` on the counted sets
  have hBne : ∀ B : Block V, B.slot = s + 1 → B ≠ Block.genesis := by
    rintro B hBs rfl
    exact Nat.succ_ne_zero s hBs.symm
  have hPayload : ∀ B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, B.slot = s + 1 → M.ac_valid_payload S.P B = true := by
    intro B hB hBs
    have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
    have hwf := ((F.nd.nodeInv_treeClosed hInvW).2 B hBT (hBne B hBs)).2.1
    exact ((F.rd.block_well_formed_iff S.P S.X B).1 hwf).1.2
  have hIncl : ∀ vote' ∈ M.included_votes (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (s + 1), ∃ B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree,
      B.slot = s + 1 ∧ vote' ∈ B.votes ∧ vote'.slot = s := by
    intro vote' hv
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel] at hv
    obtain ⟨B, ⟨hB, hBs⟩, hvB, hvs⟩ := hv
    exact ⟨B, hB, hBs, hvB, hvs⟩
  have hSupport : support_votes ⊆ votes := by
    intro vote' hv
    rcases (hCs vote').1 hv with ⟨hp, hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote').2 (Or.inl ⟨hp, hτ⟩)
    · simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_support_votes_iff M F), Nat.add_sub_cancel] at hinc
      obtain ⟨B, ⟨hB, hBs⟩, hvB, hvs⟩ := hinc
      have hvB' : vote' ∈ B.votes :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B (hPayload B hB hBs)).2.1 vote' hvB
      refine (hCv vote').2 (Or.inr ?_)
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel]
      exact ⟨B, ⟨hB, hBs⟩, hvB', hvs⟩
  have ht₁₃ : M.voteTime S.C s ≤ M.voteTime S.C (s + 1) := by omega
  have hVotes : ∀ u ∈ Hs, VotesOnceFor (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes support_votes s R u := by
    intro u hu
    obtain ⟨hp, ⟨τ, hτ, hτlt⟩, hHΦ, ⟨y, hy, hyb⟩, huniq⟩ := hHeld u hu
    obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
    have hyy : y = y' := Option.some_injective _ hyy'
    refine ⟨GoldfishVote.mk u s (H u).root,
      (hCs _).2 (Or.inl ⟨hp, ⟨τ, hτ, lt_trans hτlt h23⟩, ⟨y, hy, hyy ▸ lt_trans hy'lt h23⟩⟩),
      rfl, rfl, ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
    intro vote' hv' hi'
    rcases (hCv vote').1 hv' with ⟨hp', -⟩ | hinc
    · exact huniq vote' hp' hi'
    · obtain ⟨B, hB, hBs, hvB, hvs⟩ := hIncl vote' hinc
      obtain ⟨-, hhon, ⟨i₁, hl₁, hsent₁⟩, -, -⟩ := hHs u hu
      exact (included_vote_eq_of_owner_st M F) S A x Run _ i₁ (M.voteTime S.C s) w u B
        _ vote' E hOwner hhon (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1 (hBne B hBs) hvB hi'
        hl₁ hsent₁ hvs
  exact ⟨H_w, hHwT, hvote',
    GoldilocksCorrectness.Statements.Routines.lem2_goldfish_walkEnd_extends_majority_block
      S.C _ _ votes support_votes s _ R H_w _ Hs hStart hRootsΦ hSupport hVotes
      (by rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]; exact hVb) hWalk⟩


/-- Lemma 26, the next slot's honest Goldfish vote extends a block a voter majority voted for: the
corollary of Lemma 26b that keeps of the vote only its head. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean`.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the bound of Lemma 26b, which it calls.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the head of the Goldfish vote `w` sends at the vote time of slot `s + 1` is the root of
a block that is `R` or a descendant of `R`, when the honest voters of `Hs`, who voted for `R` or
descendants of `R`, are more than half of the voters `w` counts. -/
theorem lem26_goldfish_vote_extends_voter_majority_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (R : Block V) (w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq (H u))
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ R.AncestorEq H_w := by
  obtain ⟨H_w, -, rfl, h⟩ := (lem26b_goldfish_vote_extends_voter_majority_block_held M F U) S A x Run GST s Hs H R
    w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hVoters hHold hw hF2 hF3 hLocks hSend
  exact ⟨H_w, rfl, h⟩

end GoldilocksCorrectness.Record.Proofs.Executions

