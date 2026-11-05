module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ViableAgreement
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalVoteStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.CountAgreementStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Proofs.Executions.ViableAgreement
public import GoldilocksCorrectness.Statements.Executions.ProposalVoteStatements
public import GoldilocksCorrectness.Statements.Executions.CountAgreementStatements
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma24, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma24.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the end of the honest proposer's walk, and Lemma
24, the next slot's honest Goldfish vote names the honest proposal, composed from Lemmas 20, 22, 22a
and 23. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor CountedVotes)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff ancestorEq_of_parent?
  ghost_mem_tree_or_eq)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The honest proposal of slot `s + 1` is a block of that slot other than the genesis block, its
parent link names its parent, and that parent, where `p`'s walk ended, is in `p`'s viable tree or
is `p`'s anchor at the start `t₁` of slot `s + 1`. These are the conclusions of
`proposal_parent_extends_majority_block` that do not read the votes, from step 1 of its proof
(Lemma 19 on `p`'s tick) and the end of `p`'s walk (`ghost_mem_tree_or_eq`). They are all Lemma
24's proof reads of `p`'s walk: that `X` is `B`'s parent or an ancestor of it, the conclusion that
needs a bound on `p`'s voters, Lemma 20 derives itself. Lemma 24 cannot take that bound before
step 5: it has it only from Lemma 23 (`p` counts as many voters as `w`), which needs `w` to hold
`B`, which is derived from these.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
  `i`: the step of `p`'s tick at the start of slot `s + 1`;
- `B`: the block `p` proposed at the start of slot `s + 1`; `p`: the proposer of slot `s + 1`.

Read aloud: the block `p` put on the wire at its tick at the start of slot `s + 1` is a
non-genesis block of that slot whose parent is in `p`'s viable tree or is `p`'s anchor. -/
theorem proposal_parent_walk_end (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s i : ℕ) (B : Block V) (p : V)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    B.slot = s + 1 ∧ B ≠ Block.genesis ∧ B.parent? = some B.parent ∧
      (B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
          (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree ∨
        B.parent = M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
          ((M.slotStart S.C (s + 1) : ℕ) : Int)) := by
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
  -- the slot of `t₁`, read by the spec's clock (the model's slot of a natural-number time is the
  -- spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
      (by omega)
  -- `p`'s run and proposal, from the state its tick at the step `i` starts from (Lemma 19 over the record,
  -- from the tick's input state, which satisfies the node invariant: `p` is active at its tick)
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hti : x.tickInput p (M.slotStart S.C (s + 1)) = x.st i p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i p (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨-, -, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hInv hB₁
  rw [hslot₁, Nat.add_sub_cancel] at hWalkP
  rw [hslot₁] at hBdef
  -- `p`'s walk, `PoolHeadOf`'s, over the counted votes `ProposalCountedVotes`
  obtain ⟨votes_p, support_p, -, hW⟩ := hWalkP
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hBpar? : B.parent? = some Hp := by rw [hBdef]; rfl
  -- the end of `p`'s walk: its start or a block of the tree walked
  have hEnd := @GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq V _ M.tieBreak _ _ _ _ _ hW
  rw [hBpar]
  exact ⟨hBslot, hBne, hBpar?, hEnd.symm⟩

/-- Lemma 24, the next slot's honest vote names the honest proposal, composed (G0 over
executions). Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ComposedProposalVoteStatements.lean`.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`; Lemma 20 and
`child_mem_proposer_viable_tree` read earlier.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the Goldfish vote `w` sends at the vote time of slot `s + 1` names the block `B` the
honest proposer `p` proposed at the start of slot `s + 1`, when the honest voters of `Hs` voted for
descendants of `X`, are more than half of the voters `w` counts, `B` passes `w`'s viability test and
the two validators have the same least viable height. -/
theorem lem24_goldfish_vote_names_honest_proposal_composed (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
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
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    (hF2w : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B)
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` passes `w`'s viability test
    (hBViable : M.is_viable (x.tickInput w (M.voteTime S.C (s + 1))) B = true)
    -- the two validators have the same least viable height
    (hFloor : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) =
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1)))) :
    vote.head = B.root := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  -- the times: `t₁ = cut(s) + 2Δ`, `vt(s + 1) = t₁ + Δ`
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hc₀ : M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hmx12 : max (Δ S) Δs ≤ max (2 * Δ S) Δs := max_le_max (by omega) le_rfl
  have hcut1 : 1 ≤ M.supportCutoff S.C s := by omega
  -- the read times: `t₀ = cut(s) − max (2Δ) Δs` (Lemma 12's), `t₀' = t₁ − max Δ Δs` (Lemma 23's), `t₀ ≤ t₀'`
  have ht₀₀' : M.supportCutoff S.C s - max (2 * Δ S) Δs ≤ M.slotStart S.C (s + 1) - max (Δ S) Δs := by
    omega
  have ht₀'1 : M.slotStart S.C (s + 1) - max (Δ S) Δs + Δs ≤ M.slotStart S.C (s + 1) := by omega
  have hcR : ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have h₀₀'R : ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤
      ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast ht₀₀'
  have ht₁R : (M.slotStart S.C (s + 1) : ℝ) = (M.supportCutoff S.C s : ℝ) + 2 * (Δ S : ℝ) := by
    have : M.slotStart S.C (s + 1) = M.supportCutoff S.C s + 2 * Δ S := by omega
    rw [this]; push_cast; ring
  have hv₃R : (M.voteTime S.C (s + 1) : ℝ) = (M.slotStart S.C (s + 1) : ℝ) + (Δ S : ℝ) := by
    rw [hv₃]; push_cast; ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  -- the step forms the callees read, from the two readers (re-check 55 section 2.6)
  have hpC : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E
      (mem_activeThroughoutToTick_of_le_end_int M x R E hcut1 (by linarith) (by linarith) hp) (by linarith)
  have hwC : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E
      (mem_activeThroughoutToTick_of_le_end_int M x R E hcut1 (by linarith) (by linarith) hw) (by linarith)
  have hpF : ∃ kP : ℕ, x.lbl kP = Event.tick p (M.slotStart S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kP →
        p ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E hp (by linarith)
  have hwF : ∃ kW : ℕ, x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kW →
        w ∈ A.active j :=
    tick_window_of_activeThroughoutToTick_int M x R E hw (by linarith)
  have hHoldW : w ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hw
      (a' := M.slotStart S.C (s + 1) - max (Δ S) Δs) (e := M.slotStart S.C (s + 1) - max (Δ S) Δs + Δs)
      (by push_cast; linarith) (by
        have : ((M.slotStart S.C (s + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤ (M.slotStart S.C (s + 1) : ℝ) := by
          exact_mod_cast ht₀'1
        linarith)
    rw [Nat.cast_add] at h
    exact h
  have hwR := tick_window_ahead_of_activeThroughoutToTick_int M x R E hw (c := M.slotStart S.C (s + 1))
    (by linarith)
  -- the two ticks Lemma 11 reads
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨kW, hkW, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  have hpT : p ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact E.not_mem_corrupted_of_tick hl
  have hwT : w ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkW]
    exact E.not_mem_corrupted_of_tick hkW
  have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) :=
    (lem11_node_invariant M F S A x R E (x.tickStep w (M.voteTime S.C (s + 1))) w hwT).1
  -- the real times of the ticks the roots rows read
  have hkWt : (M.voteTime S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkW]
    exact (E.tick_active kW w _ hkW).2.1
  -- the finalized blocks and the fork-choice roots (Lemma 46)
  have hF2p : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ p
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ w
  -- step 1: the end of `p`'s walk
  obtain ⟨-, -, hBpar?, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hRXp : (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root.AncestorEq X :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) hApX
  have hFXp : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq X :=
    ancestorEq_trans hF2p hRXp
  -- step 2: `B`'s parent is in `p`'s tree, and `p`'s finalized block is an ancestor of `B`
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
  -- step 3: `p` holds `B` after its tick (Lemma 22a), and `w` at its vote tick (Lemma 22)
  have hBp : B ∈ (x.st (i + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R s i B p
      E hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B :=
    ancestorEq_trans hFroot hF2w
  have hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem22_proposal_held_by_voter M F U) S A x R GST s i B p
      w E hNet hSkew hRedeliver hRoots hParent (by omega) hwR hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- step 4: `B` is in `w`'s frame tree, and is a viable head there
  have hBΦ : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBw, hFwB⟩
  have hBfl : M.head_height_floor (x.tickInput w (M.voteTime S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.is_viable_iff M F) S.C S.P S.X _ hInvW B hBw).1
      hBViable
  have hBVH : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvW B).2
      ⟨hBw, hFwB, hF2w, hBfl⟩
  -- step 5: the two validators count alike (Lemma 23)
  have hCount := (GoldilocksCorrectness.Record.Proofs.Executions.lem23_proposer_and_voter_count_alike M F U)
    S A x R GST s B p w E hNet hSkew hRedeliver Sy hRoots hParent (by omega) hpF hwF hHoldP hHoldW hPropose hBΦ
    hOnly
  -- step 6: the two validators agree on the viable heads along the path, past the root of `w`'s
  -- fork choice
  have hViableAgree := (viable_heads_agree_of_floor_eq_at M F) S A x R E
    (x.tickStep p (M.slotStart S.C (s + 1))) (x.tickStep w (M.voteTime S.C (s + 1))) X B p w hParentHeld
    hBw hFXp hRXp hFloor hpT hwT
  -- step 7: every child in `w`'s viable tree of a block of the path, other than `B`, is in `p`'s
  have hpTime : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤
      x.time (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hl]
    have := (E.tick_active i p _ hl).2.2
    linarith
  have hChild := (child_mem_proposer_viable_tree M F U) S A x R GST s X B p w E hNet hSkew hRedeliver Sy
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hpTime hRoots) hParent
    (by omega) hpF hwF hHoldW hOnly hEnd hApX (le_of_eq hFloor)
  -- step 8: Lemma 20, with roots up to the two ticks to the support cutoff of slot `s`
  obtain ⟨kpC, hkpC, -⟩ := id hpC
  obtain ⟨kwC, hkwC, -⟩ := id hwC
  have hRoots20 : RootsNameBlocksUntil M A x (max (x.time (x.tickStep p (M.supportCutoff S.C s)))
      (x.time (x.tickStep w (M.supportCutoff S.C s)))) := by
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [(tickStep_eq_of_lbl M) x E hkpC, (tickStep_eq_of_lbl M) x E hkwC]
    have h1 := (E.tick_active kpC p _ hkpC).2.2
    have h2 := (E.tick_active kwC w _ hkwC).2.2
    exact max_le (by linarith) (by linarith)
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem20_goldfish_vote_names_honest_proposal M F U) S
    A x R GST s Hs H X B p w vote E hNet hSkew hRedeliver Sy hΔs hRoots20 hParent hOwner hGST hHs
    hVoters hHold hpC hwC hPropose hSend hBw hF3p hApX hLocksW hBVH hViableAgree
    (fun vp sp vw sw h₁ h₂ => ⟨fun Y hXY hRY _ D hD => (hCount vp sp vw sw h₁ h₂).1 D
        (ancestorEq_trans hFXp (ancestorEq_trans hXY (ancestorEq_of_parent? hD)))
        (ancestorEq_trans hFroot (ancestorEq_trans hRY (ancestorEq_of_parent? hD))),
      (hCount vp sp vw sw h₁ h₂).2⟩)
    (fun _ _ _ Y hXY _ hYB D hD hDpar hDB _ => hChild Y hXY hYB D hD hDpar hDB)

end GoldilocksCorrectness.Record.Proofs.Executions

