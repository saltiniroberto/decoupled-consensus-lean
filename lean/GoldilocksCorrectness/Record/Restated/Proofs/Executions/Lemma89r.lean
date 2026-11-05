module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightInvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Statements.Executions.HeightInvariantStatements
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89r, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89r.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the viable head of the anchor, the ordered
`head_height_floor` under unordered delivery, the lock box from the frame, and Lemma 89r, the quiet
round's frame relative to the honest proposal. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_le_of_le
  slot_add_two_le_of_delivery supportCutoff_eq supportCutoff_le_slotStart_succ voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (head_height_floor_initial)

open GoldilocksCorrectness.Proofs.Routines (initial_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)



open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxTwo ChainStatesComputed
  CountedVotes HeightCacheBounds)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_compatible genesis_ancestorEq ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The kit -/

/-- The anchor of `p`'s walk on its state before `t` has a viable head of `p`'s frame among its
descendants: a block `p` holds that is the anchor or a descendant of it, the fork-choice root or a
descendant of it, at a chain-state height at least the `head_height_floor`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator;
- `A`: the AC state the anchor reads; `t'`: the time it reads.

Read aloud: the anchor of `p`'s walk has a viable head of `p`'s frame among its descendants. -/
theorem anchor_has_viable_head (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (Env : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (p : V) (E : Finset M.LE) (t' : Time) :
    ∃ W ∈ (x.stateBefore t p).tree,
      (AnchorAt M (M.fg_to_ac (x.stateBefore t p)) E t').AncestorEq W ∧
      (M.get_fc_root (x.stateBefore t p)).AncestorEq W ∧
      M.head_height_floor (x.stateBefore t p) ≤ (M.chainStateOf S.C W).h := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) p).1
  have hvh : ∀ W ∈ (M.fg_to_ac (x.stateBefore t p)).viable_heads,
      W ∈ (x.stateBefore t p).tree ∧ (M.get_fc_root (x.stateBefore t p)).AncestorEq W ∧
      M.head_height_floor (x.stateBefore t p) ≤ (M.chainStateOf S.C W).h := by
    intro W hW
    obtain ⟨hT, -, hR, hfl⟩ :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _ hInv W).1 hW
    exact ⟨hT, by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hR, hfl⟩
  -- the anchor over `p`'s frame with the lock entries `E` is its fgroot or a block of its viable tree
  rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
      (M.fg_to_ac (x.stateBefore t p)) E t' with h | h
  · obtain ⟨W, hW⟩ := (frame_has_viable_head M F) S A x R Env t p
    obtain ⟨hT, hR, hfl⟩ := hvh W hW
    refine ⟨W, hT, ?_, hR, hfl⟩
    rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact hR
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at h
    obtain ⟨-, -, W, hW, hAW⟩ := h
    obtain ⟨hT, hR, hfl⟩ := hvh W (Finset.mem_inter.1 hW).2
    exact ⟨W, hT, hAW, hR, hfl⟩

/-- Before `t`, when `v`'s fork-choice root is `B` or an ancestor of `B` and its
`head_height_floor` is at most `B`'s chain-state height `H`, `v`'s cache `h_j` is less than `H`, or
its record holds no lock at `H`, or its lock at `H` is the root of the block that took `B`'s chain
into `H`.

Why: in boxes 1 and 3 the cache `h_j` is less than the `head_height_floor`; in box 2 the
`head_height_floor` is `h_j`, and when it equals `H` the lock at `H` is on the justified block
(`lockBox_of_one_justification`), the fork-choice root, which took `B`'s chain into `H`
(`entry_block_of_boxTwo`, or at `H = 1` the genesis block).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `t`: the time;
  `v`: the validator; `B`: the block.

Read aloud: when `v`'s fork-choice root is `B` or an ancestor of `B` and its `head_height_floor` is
at most `B`'s chain-state height `H`, `v` holds no lock at `H` other than on the root of the block
that took `B`'s chain into `H`, or its cache `h_j` is less than `H`. -/
theorem lockBox_of_frame (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) (B : Block V)
    -- fewer than a third of the validators have been in the adversary set up to `t`
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) t)
    -- `v`'s fork-choice root before `t` is `B` or an ancestor of `B`
    (hRoot : (M.get_fc_root (x.stateBefore t v)).AncestorEq B)
    -- `v`'s `head_height_floor` before `t` is at most `B`'s chain-state height
    (hFloor : M.head_height_floor (x.stateBefore t v) ≤ (M.chainStateOf S.C B).h) :
    (x.stateBefore t v).justifiedHeight < (M.chainStateOf S.C B).h ∨
    (x.stateBefore t v).sentLock (M.chainStateOf S.C B).h = none ∨
    (x.stateBefore t v).sentLock (M.chainStateOf S.C B).h = some
      (M.chainStateOf S.C B).T_h.root := by
  obtain ⟨⟨D, hDT, hDJ, hDj⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t v
  have hCB : HeightCacheBounds M S.C (x.stateBefore t v) :=
    fun _ hB => le_hMax M hB
  have hDh : (M.chainStateOf S.C D).h ≤ hMax M S.C (x.stateBefore t v) := by
    exact hCB D hDT
  have hD47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  have hB47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.1
  have hjm : (x.stateBefore t v).justifiedHeight + 1 ≤ hMax M S.C (x.stateBefore t v) := by
    rw [hDj]
    unfold Height at *
    omega
  by_cases hm : hMax M S.C (x.stateBefore t v) = (x.stateBefore t v).justifiedHeight + 1
  · cases hc : M.fg_contest (x.stateBefore t v) with
    | true =>
        obtain ⟨-, -, hfl⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxThree_of_core M F) S.C S.P S.X _ (by exact (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) v).1) hc
        left
        rw [hfl] at hFloor
        unfold Height at *
        omega
    | false =>
        have hBox : BoxTwo M S.C (x.stateBefore t v) (x.stateBefore t v).justified := ⟨hm, hc, rfl⟩
        have hSh := (GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxTwo_of_core M F) S.C S.P S.X _ (by exact (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) v).1) _ hBox
        rw [hSh.2] at hFloor
        rw [hSh.1] at hRoot
        by_cases hlt : (x.stateBefore t v).justifiedHeight < (M.chainStateOf S.C B).h
        · exact Or.inl hlt
        right
        have hH : (M.chainStateOf S.C B).h = hMax M S.C (x.stateBefore t v) - 1 := by
          unfold Height at *
          omega
        cases hl : (x.stateBefore t v).sentLock (M.chainStateOf S.C B).h with
        | none => exact Or.inl rfl
        | some T' =>
          right
          have hT' := (lockBox_of_one_justification M F Fx) S A x R E t v v _ T' hAdv hBox
            (by rw [← hH]; exact hl)
          rw [hT']
          by_cases hJg : (x.stateBefore t v).justified = Block.genesis
          · -- the justified block is the genesis block, so `H = 1`
            have hDJg : (M.chainStateOf S.C D).J = Block.genesis := by rw [← hDJ]; exact hJg
            have hj1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
              rcases Nat.eq_zero_or_pos (M.chainStateOf S.C D).h_j with h0 | hpos
              · exfalso
                unfold Height at *
                omega
              · exact hpos
            have hgh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 hj1
            rw [hDJg] at hgh
            have hg1 : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
              (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
            have hHg : (M.chainStateOf S.C (Block.genesis : Block V)).h = (M.chainStateOf S.C B).h := by
              unfold Height at *
              omega
            have hTh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Block.genesis B).2.2.2.2
              (genesis_ancestorEq B) hHg
            have hTg : (M.chainStateOf S.C (Block.genesis : Block V)).T_h = Block.genesis :=
              (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_T_h M F) S.C
            rw [hJg, ← hTh, hTg]
          · rw [(entry_block_of_boxTwo M F) S A x R E t v B _ hBox hJg hRoot hH]
  · left
    have hb : BoxOne M S.C (x.stateBefore t v) := by
      show (x.stateBefore t v).justifiedHeight + 1 < hMax M S.C (x.stateBefore t v)
      unfold Height at *
      omega
    have hSh := ((GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxOne_of_core M F) S.C S.P S.X _ (by exact (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) v).1) hb).2
    rw [hSh.2] at hFloor
    unfold Height at *
    omega

/-- The honest proposal of slot `s₀ + 1` is on the chain of every block of a family whose blocks
every slot-`s₀` vote of `Hs` extends, when the family holds `p`'s anchor and `p`'s frame has a
viable head on the chain of each of its blocks: every block of the family is `B`'s parent or an
ancestor of it.

Why: a vote of a member of `Hs` extends both a block `C` of the family and `p`'s anchor, so the two
are ordered. When `C` is an ancestor of the anchor, the anchor is an ancestor of `B`'s parent
(the walk starts there). Otherwise `p`'s walk passes `C`
(`proposal_parent_extends_majority_block` with `X := C`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s₀`: the slot of the votes;
- `Hs`: the voters; `𝓒`: the family; `B`: the proposal of slot `s₀ + 1`; `p`: its proposer.

Roots name blocks until the real time of `p`'s tick to the support cutoff of slot `s₀`: the proof compares two
blocks a member of `Hs` holds at its tick to the vote time of slot `s₀` (before that tick, by `hSkew`), and the
proposer's walk (`proposal_parent_extends_majority_block` at slot `s₀`) reads blocks held up to that tick.

Restated: the members' honesty is read at `p`'s tick to
the start of slot `s₀ + 1`, the members are active through the sync window that starts `max (2 * Δ S) Δs` before the
support cutoff of slot `s₀`, and `p` ticks to that cutoff and is active from the window's
start up to that tick: the hypotheses of `proposal_parent_extends_majority_block`, which the proof calls.

Read aloud: every block of the family is the honest proposal's parent or an ancestor of it. -/
theorem family_ancestorEq_proposal_parent (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ : ℕ) (Hs : Finset V) (𝓒 : Block V → Prop)
    (B : Block V) (p : V)

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `p`'s own tick to the support cutoff of slot `s₀`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C s₀))))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    -- each member of `Hs` is in the committee of slot `s₀`, outside the adversary set at `p`'s tick to the start of
    -- slot `s₀ + 1`, and put a slot-`s₀` vote on the wire at its tick at the vote time of slot `s₀`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s₀ ∧ u ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s₀ + 1))) ∧
      ∃ vote : GoldfishVote V, ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- each such vote names a block its voter holds that descends from every block of the family
    (hExt : ∀ C : Block V, 𝓒 C → ∀ u ∈ Hs, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s₀)).tree,
        vote = GoldfishVote.mk u s₀ H_u.root ∧ C.AncestorEq H_u)
    -- the validators with a slot-`s₀` vote in `p`'s pool before its proposal are fewer than twice
    -- `Hs`
    (hVotersP : M.voters_count
        (M.votesHeldSet (x.tickInput p (M.slotStart S.C (s₀ + 1))) s₀) < 2 * Hs.card)
    -- every member of `Hs` is active at every step at a real time from `max (2 * Δ S) Δs` before the support cutoff
    -- of slot `s₀` to one sync delay after that
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` ticks to the support cutoff of slot `s₀` at `kR` and is active at every step from the real time
    -- `max (2 * Δ S) Δs` before that cutoff up to `kR`
    (hp : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s₀) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j)
    -- `p` put `B` on the wire at its tick at the start of slot `s₀ + 1`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s₀ + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `p`'s frame has a viable head on the chain of every block of the family
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
          C.AncestorEq W)
    -- the family holds `p`'s anchor
    (hAnchor : 𝓒
        (M.get_anchor (x.tickInput p (M.slotStart S.C (s₀ + 1)))
            ((M.slotStart S.C (s₀ + 1) : ℕ) : Int))) :
    ∀ C : Block V, 𝓒 C → C.AncestorEq B.parent := by
  intro C hC
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hv₀ : M.voteTime S.C s₀ = M.slotStart S.C s₀ + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hc₀ : M.supportCutoff S.C s₀ = M.voteTime S.C s₀ + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hAP := (get_anchor_ancestorEq_proposal_parent M F) S A x R E (s₀ + 1) i B p hl hsent
  obtain ⟨kR, hkR, hpkR⟩ := hp
  have hkRt := (E.tick_active kR p _ hkR).2.1
  have hRootsK : RootsNameBlocksUntil M A x (x.time kR) := by
    rw [← (tickStep_eq_of_lbl M) x E hkR]; exact hRoots
  -- a member's two blocks named by one root are one block
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨-, -, vote₀, i₀, hl₀, hs₀⟩ := hHs u₀ hu₀
  obtain ⟨H₁, hH₁T, hv₁, hCH₁⟩ := hExt C hC u₀ hu₀ vote₀ ⟨i₀, hl₀, hs₀⟩
  obtain ⟨H₂, hH₂T, hv₂, hAH₂⟩ := hExt _ hAnchor u₀ hu₀ vote₀ ⟨i₀, hl₀, hs₀⟩
  have hroot : H₁.root = H₂.root := by
    rw [hv₁] at hv₂
    exact (GoldfishVote.mk.inj hv₂).2.2
  obtain ⟨hu₀a, -, hi₀t⟩ := E.tick_active i₀ u₀ _ hl₀
  have hu₀c : u₀ ∉ A.corrupted i₀ := (Activity.mem_active.1 hu₀a).2
  have hi₀k : x.time i₀ ≤ x.time kR := by
    have : ((M.voteTime S.C s₀ : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by
      exact_mod_cast hc₀.symm
    linarith
  have hti : x.tickStep u₀ (M.voteTime S.C s₀) = i₀ := (tickStep_eq_of_lbl M) x E hl₀
  have hH₁T' : H₁ ∈ (x.st i₀ u₀).tree := by rw [← hti]; exact hH₁T
  have hH₂T' : H₂ ∈ (x.st i₀ u₀).tree := by rw [← hti]; exact hH₂T
  have hH : H₁ = H₂ := hRootsK _ _ ((inHonestTreeBy_of_st M F) x R E hu₀c hi₀k hH₁T')
    ((inHonestTreeBy_of_st M F) x R E hu₀c hi₀k hH₂T') hroot
  subst hH
  rcases ancestorEq_compatible hCH₁ hAH₂ with hCA | hAC
  · exact ancestorEq_trans hCA hAP
  · -- `p`'s walk passes `C`
    have hex : ∀ u ∈ Hs, ∃ H_u : Block V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
        H_u ∈ (x.tickInput u (M.voteTime S.C s₀)).tree ∧ C.AncestorEq H_u := by
      intro u hu
      obtain ⟨-, -, vote, i', hl', hs'⟩ := hHs u hu
      obtain ⟨H_u, hT, hv, hCH⟩ := hExt C hC u hu vote ⟨i', hl', hs'⟩
      subst hv
      exact ⟨H_u, ⟨i', hl', hs'⟩, hT, hCH⟩
    choose Hc hHc using hex
    let Hf : V → Block V := fun u => if h : u ∈ Hs then Hc u h else C
    have hHf : ∀ u (hu : u ∈ Hs), Hf u = Hc u hu := fun u hu => dif_pos hu
    exact ((proposal_parent_extends_majority_block M F U) S A x R GST s₀ i Hs Hf C B p E hNet hSkew hRedeliver Sy
      hΔs hRoots hParent hOwner hGST
      (fun u hu => by
        rw [hHf u hu]
        exact ⟨(hHs u hu).1, (hHs u hu).2.1, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩)
      (fun votes_p support_p hP => by rw [hP.1]; exact hVotersP) hHold ⟨kR, hkR, hpkR⟩ hl hsent
      (hFrameP C hC) hAC).1

/-- **The proposer clause gives `hFrameQ`.** When the round is quiet relative to its own
confirmations and `B` is an ancestor of, or equal to, every confirmation of slot `s'' − 2` that a
member of `Hon (s'' − 2)` saved (the chain invariant relative to `B` at that slot), the next
proposer's fork-choice root, in the state its tick to the start of slot `s''` starts from, is
compatible with `B` and, when it is `B` or an ancestor of `B`, some viable head of its frame is `B`
or a descendant of `B`: the hypothesis `hFrameQ` of `lem80wq_round_height_advances_steps` at
`q := S.P.proposer s''`.

Why: the root and `B` are both ancestors of, or equal to, that confirmation `C`, so they are
comparable; the viable head on `C`'s chain is on `B`'s.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.

Read aloud: in a round quiet relative to its own confirmations, the next proposer's frame satisfies
the proposer clause relative to `B`. -/
theorem frameQ_of_quietRoundOnConfirmations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    (hQuiet : QuietRoundOnConfirmations M S A x Hon B s s'')
    -- `B` is an ancestor of, or equal to, every confirmation of slot `s'' − 2` a member of
    -- `Hon (s'' − 2)` saved
    (hChainB : ∀ C : Block V, (∃ v ∈ Hon (s'' - 2),
      (x.tickOutput v (M.supportCutoff S.C (s'' - 1))).savedConfirmation (s'' - 2) = some C)
          →
      B.AncestorEq C) :
    (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).fc_root.compatible B =
      true ∧
    ((M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).fc_root.AncestorEq B →
      ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).tree,
        W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).viable_heads ∧
        B.AncestorEq W) := by
  obtain ⟨C, hCsaved, hroot, W, hWtree, hWviable, hCW⟩ := hQuiet.2.2.2.2
  have hBC : B.AncestorEq C := hChainB C hCsaved
  refine ⟨(compatible_iff _ _).2 (ancestorEq_compatible hroot hBC), fun _ => ?_⟩
  exact ⟨W, hWtree, hWviable, ancestorEq_trans hBC hCW⟩

/-- **The frame of a member at the slot before the round, relative to the proposal.** When `w`
holds the proposal `B` of slot `s₀ + 1` in the state its tick to the vote time of slot `s₀ + 1`
starts from, the fork-choice root of that state is `B` or an ancestor of `B` with its
`head_height_floor` at most the chain-state height of `B`, and the fork-choice root of the state its tick to the support cutoff of slot `s₀ + 2` starts
from is `B` or an ancestor of `B`, then `StepFrameAt M S Sched x B s₀ w` holds.

Why: the root is compatible with `B`; `B` is in `w`'s voter tree of slot `s₀ + 1` (a block of the
frame tree, stamped, of that slot) and is a viable head (its chain state is its own by Lemma 11,
at least the `head_height_floor`); the finalized block is the root or an ancestor of it (Lemma 46),
so it is compatible with `B`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `B`: the proposal; `s₀`: the slot before the proposal's; `w`: the member.

Read aloud: a member holding the proposal `B` of slot `s₀ + 1` with a frame compatible with it
satisfies `StepFrameAt` relative to `B` at slot `s₀ + 1`. -/
theorem stepFrameAt_proposal_of_quiet (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (B : Block V) (s₀ : ℕ) (w : V)
    -- `B` is a block of slot `s₀ + 1` that `w` holds before the vote time of that slot
    (hslot : B.slot = s₀ + 1)
    (hHeld : B ∈ (x.tickInput w (M.voteTime S.C (s₀ + 1))).tree)
    -- `w`'s fork-choice root before that vote time is `B` or an ancestor of `B`, and its
    -- `head_height_floor` then is at most the chain-state height of `B`
    (hRoot : (M.get_fc_root (x.tickInput w (M.voteTime S.C (s₀ + 1)))).AncestorEq B)
    (hFloor : M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ≤
      (M.chainStateOf S.C B).h)
    -- the fork-choice root of the state `w`'s tick to the support cutoff of slot `s₀ + 2` starts
    -- from is `B` or an ancestor of `B`
    (hRootA : (M.get_fc_root (x.tickInput w (M.supportCutoff S.C (s₀ + 2)))).AncestorEq B) :
    StepFrameAt M S A x B s₀ w := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.tickStep w (M.voteTime S.C (s₀ + 1))) w).1
  have hF : (x.tickInput w (M.voteTime S.C (s₀ + 1))).finalized.AncestorEq B :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E (x.tickStep w (M.voteTime S.C (s₀ + 1))) w) hRoot
  have hBtree : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₀ + 1)))).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hHeld, hF⟩
  -- `B` is in `w`'s voter tree of slot `s₀ + 1` (a stamped block of the frame's tree, of that slot)
  -- and a viable head (at a chain-state height at least the `head_height_floor`)
  refine ⟨(compatible_iff _ _).2 (Or.inl (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hRoot)),
    fun hR => ⟨B, ?_, ?_, ancestorEq_refl B⟩, ?_⟩
  · obtain ⟨τ, τ', hτ, -, -⟩ := (ancestor_blockStamp_le M F) S A x R E
      (x.tickStep w (M.voteTime S.C (s₀ + 1))) w B B hHeld (ancestorEq_refl B)
    exact ⟨hBtree, τ, hτ, Or.inr ⟨B, hBtree, hslot, ancestorEq_refl B⟩⟩
  · exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _ hInv B).2
      ⟨hHeld, hF, hR, hFloor⟩
  · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E
        (x.tickStep w (M.supportCutoff S.C (s₀ + 2))) w) hRootA))

end GoldilocksCorrectness.Record.Proofs.Executions

