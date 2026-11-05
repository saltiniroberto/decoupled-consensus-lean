module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma17, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma17.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 17, the next slot's honest Goldfish vote
extends a block a committee majority voted for. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes
  votesOnceInPoolFor_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes AwakeFor AnchorAt
  VoterTreeAt)
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
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible committee_card_le_of_majority)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Lemma 17, the next slot's honest Goldfish vote extends a block a committee majority voted
for. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean`. It is Lemma 26 with the
committee majority, which gives Lemma 26's voter bound because every vote `w` counts is from the
slot-`s` committee (the admission invariant), and its lock condition through Lemma 5.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 and Lemma 26 calls at
slot `s` it passes the premise to.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the head of the Goldfish vote `w` sends at the vote time of slot `s + 1` is the root of
a block that is `R` or a descendant of `R`, when the honest voters of `Hs`, who voted for `R` or
descendants of `R`, are a majority of the slot-`s` committee. -/
theorem lem17_goldfish_vote_extends_majority_block (U : UniformSchedule M.toSlotLayout)
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
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
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
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ R.AncestorEq H_w := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  -- `w`'s vote tick, and the state it reads
  obtain ⟨i, hl, hm⟩ := id hSend
  obtain ⟨-, n₀, sent₀, hrun₀, hvote₀⟩ := (tick_send_of_honestSendAt M F Run E) hl hm
  have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x Run E i w hwi).1
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x Run E i w
  -- the times; the slot of `t₃`, read by the spec's clock (the model's slot of a natural-number
  -- time is the spec's, `U`)
  have hΔ := one_le_Δ S
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hslot₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  -- step 1: the case `R` an ancestor of `w`'s finalized block: `w`'s vote is for the end `H_w` of
  -- `HeadOf`'s walk (Lemma 14 over the record, the field `tick_vote_head` of `F.tk3`, from the
  -- tick's input state), which is the anchor or a descendant of it; the anchor is the fgroot or a
  -- descendant of it, and the fgroot is `w`'s finalized block or a descendant of it
  rcases (compatible_iff _ _).1 (compatible_of_ancestorEq_compatible hFroot hF2) with hFR | hRF
  swap
  · obtain ⟨-, -, -, -, -, H_w, ⟨votes, support_votes, -, hWalk⟩, hhead⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n₀ _ sent₀ vote hrun₀
        hInvW hvote₀
    have hAH := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1
    have hRA : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq
        (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n₀.lockEntries
          ((M.voteTime S.C (s + 1) : ℕ) : Int)) := by
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n₀.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | h
      · rw [h]
        exact ancestorEq_refl _
      · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
    exact ⟨H_w, hhead, ancestorEq_trans hRF (ancestorEq_trans hFroot (ancestorEq_trans hRA hAH))⟩
  -- the case `w`'s finalized block an ancestor of `R`, hence of every `H u`
  have hF1 : ∀ u ∈ Hs, (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq (H u) :=
    fun u hu => ancestorEq_trans hFR (hHs u hu).2.2.2.2
  -- step 2: the delivered votes, held early at the tick input (Lemma 12 in the step form)
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) s (H u) u :=
    (lem12_honest_vote_delivered_until_of_steps M F U) S A x Run GST s (M.voteTime S.C (s + 1)) Hs H w
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST
      (by
        have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
        have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S s
        omega) i hl
      (fun u hu => ⟨(hHs u hu).1, (tickStep_eq_of_lbl M) x E hl ▸ (hHs u hu).2.1, (hHs u hu).2.2.1,
        (hHs u hu).2.2.2.1⟩)
      hHold hw hF1
  -- step 3: the lock condition, by Lemma 5 at the revocation every outcome of the tick at `t₃`
  -- ran (the field `tick_voteTime_locks` of `F.tk2`, at the node invariant of the tick input)
  have hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true := by
    intro n' sent hrun hAwake e he _
    have hRevoke := F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n' sent hrun hInvW
      (by rw [hslot₃]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s + 1))
      (by rw [hslot₃]; exact hAwake)
    rw [hslot₃] at hRevoke
    refine ((GoldilocksCorrectness.Record.Statements.Routines.lem5_revoke_locks_entries_compatible F) R Hs
      (Nat.le_add_left 1 s) (fun u hu => ?_) (committee_card_le_of_majority hMajority) hRevoke e he).2
    obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u hu
    exact ⟨_, hp, rfl, ⟨y, hy⟩, ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, huniq⟩
  -- step 4: the voter bound, every counted vote being from the slot-`s` committee (a pool vote by
  -- the admission invariant, an included vote by its block's payload, the block well formed by
  -- the node invariant)
  have hBne : ∀ B : Block V, B.slot = s + 1 → B ≠ Block.genesis := by
    rintro B hBs rfl
    exact Nat.succ_ne_zero s hBs.symm
  have hPayload : ∀ B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, B.slot = s + 1 → M.ac_valid_payload S.P B = true := by
    intro B hB hBs
    have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
    have hwf := ((F.nd.nodeInv_treeClosed hInvW).2 B hBT (hBne B hBs)).2.1
    exact ((F.rd.block_well_formed_iff S.P S.X B).1 hwf).1.2
  have hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card := by
    intro votes support_votes hCounted
    have hCv := hCounted.1
    simp only [Nat.add_sub_cancel] at hCv
    refine GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F
      (Q := S.P.committee s) (fun vote' hv => ?_) hMajority
    rcases (hCv vote').1 hv with ⟨hp, -⟩ | hinc
    · exact (pool_committee_of_exec M F) S A x Run E _ w s vote' hp
    · simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel] at hinc
      obtain ⟨B, ⟨hB, hBs⟩, hvB, -⟩ := hinc
      have h := ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B (hPayload B hB hBs)).2.2 vote' hvB
      rw [hBs, Nat.add_sub_cancel] at h
      exact h
  -- step 5: Lemma 26
  exact (lem26_goldfish_vote_extends_voter_majority_block M F U) S A x Run GST s Hs H R w vote E hNet hSkew hRedeliver
    Sy hΔs hRoots hParent hOwner hGST hHs hVoters hHold hw hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Proofs.Executions

