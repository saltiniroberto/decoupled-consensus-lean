module
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeSends

@[expose] public section

/-!
- `honest_vote_form`: a Goldfish vote a validator's tick puts on the wire at the vote time of slot
  `s'` is that validator's, of slot `s'`;
- `slot_lt_of_ancestorEq_of_treeClosed`: a strict ancestor of a block of a closed tree has a
  smaller slot;
- `record_content_sent`: every content of a validator's anti-slashing record is the content of a
  well-formed attestation of that validator, put on the wire by its own tick;
- `proposal_viable_head_at`: a block a voter holds early, on its root's chain and at least at its
  `head_height_floor` (the least chain-state height a viable block may have), is in its voter tree and a viable head of its frame;
- `get_anchor_ancestorEq_proposal_parent`: a proposer's anchor is the parent of its proposal or an
  ancestor of it;
- `update_lock_entries_ancestorEq`: the live lock entries an honest update of slot `s + 1` leaves
  are on the block it saves for slot `s` or an ancestor of it, when that block is of slot `s` and
  the live entries of the revocation of slot `s + 1` are compatible with it.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_slot
  viewFreeze_cast voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (initial_eq is_live_iff on_ac_message_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (signingHistory_initial_eq)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (propose_block_sends record_awake_frame on_block_eq)
open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)
open GoldilocksCorrectness.Proofs.Routines (DREBEmits)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## What a tick writes into the anti-slashing record -/

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (on_block_eq slot_lt_of_ancestorEq_of_treeClosed)
open GoldilocksCorrectness.Statements.Routines (TreeClosed)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks FrameShape VoterTreeAt
  RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_genesis_iff ancestorEq_node_iff RecordFromSent tick_record_rel)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The times -/

/-! ## A Goldfish vote of a tick -/

/-- **Kit fact, the form of a tick's Goldfish vote.** A Goldfish vote a validator `u`'s tick puts
on the wire at the vote time of slot `s'` is `u`'s, of slot `s'` (Lemma 14, with Lemma 11 for the
validator field).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the validator;
  `vote`: the vote.

Read aloud: an honest tick's vote names its own validator and slot. -/
theorem honest_vote_form (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s' : ℕ) (u : V) (vote : GoldfishVote V)
    -- `u` put `vote` on the wire at its tick at the vote time of slot `s'`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    vote.val_index = u ∧ vote.slot = s' := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hslot : S.C.slot ((voteTime S s' : ℕ) : Int) = s' :=
    slot_eq_of_mem S (by omega) (by omega)
  obtain ⟨i, hl, hm⟩ := hSend
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  obtain ⟨-, hvi, hvs, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  have hnv : (tickInputState x i (voteTime S s') u).v = u := by
    have h := (lem11_node_invariant S Sched x i u).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hnv] at hvi
  rw [hslot] at hvs
  exact ⟨hvi, hvs⟩

/-! ## The slots along a closed tree -/

/-- **Kit fact, an attestation a tick sends is well formed.** An attestation that `v`'s tick at `t`
puts on the wire is well formed: the validator client built it at the height of the chain state of
a source in `v`'s tree (Lemma 49), which is at least `1` (Lemma 47 (a), with Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `t`: the time;
  `v`: the validator; `a`: the attestation.

Read aloud: honest ticks send well-formed attestations. -/
theorem tick_attestation_well_formed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i t : ℕ) (v : V) (a : Attestation V)
    -- the step `i` is the tick at `t`, and put `v`'s attestation `a` on the wire
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    attestation_well_formed a = true := by
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hsent
  obtain ⟨-, fi, source, hfi, hsrc, hbuilt, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  have hSeq := (tickInputState_frame x i t v).1
  have hsT : source ∈ (x[i][v].st).S.T := by
    rw [← hSeq]
    exact ((mem_fg_to_ac_tree _ _).1
      (GoldilocksCorrectness.Proofs.Routines.ac_to_fg_source_mem hfi hsrc)).1
  have hσ : (x[i][v].st).S.σ source = chainStateOf S.C source :=
    (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1 source hsT
  have h1 : 1 ≤ ((tickInputState x i t v).S.σ source).h := by
    rw [hSeq, hσ]
    exact (lem47_chain_state_heights S.C source source).1.1
  exact GoldilocksCorrectness.Statements.Routines.create_attestation_well_formed _ _ _ _ _ _ _ a
    h1 hbuilt

/-! ## The record's contents were sent -/

/-- Every content of a validator's record at the step `i` is the content of a well-formed
attestation of that validator that its tick at a step `j < i` put on the wire, awake and honest
then: by induction on the step, from the initial record, which holds none, through `step_cases`
(a delivery keeps the record, and a tick writes only what it sends, `tick_record_rel`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `i`: the step. -/
theorem record_content_sent_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (v : V) (i : ℕ) :
    ∀ b ∈ (x[i][v].st).Λ.sent, ∃ (j t' : ℕ) (a : Attestation V), j < i ∧
      x.lbl j = AtomicAction.tickAllAwake t' ∧
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent ∧
      a.val_index = v ∧ a.content = b ∧ attestation_well_formed a = true := by
  induction i with
  | zero =>
      intro b hb
      rw [getElem_zero_st, initial_eq, signingHistory_initial_eq] at hb
      exact absurd hb (Finset.notMem_empty b)
  | succ i ih =>
      intro b hb
      have lift : (∃ (j t' : ℕ) (a : Attestation V), j < i ∧
          x.lbl j = AtomicAction.tickAllAwake t' ∧
          v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent ∧
          a.val_index = v ∧ a.content = b ∧ attestation_well_formed a = true) →
          ∃ (j t' : ℕ) (a : Attestation V), j < i + 1 ∧
          x.lbl j = AtomicAction.tickAllAwake t' ∧
          v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent ∧
          a.val_index = v ∧ a.content = b ∧ attestation_well_formed a = true := by
        rintro ⟨j, t', a, hj, h⟩
        exact ⟨j, t', a, by omega, h⟩
      rcases step_cases x i v with h | ⟨t, n', sent, hl, hmem, hrun, h⟩ | ⟨sm, -, -, -, h⟩
      · rw [h] at hb
        exact lift (ih b hb)
      · rw [h] at hb
        have hrel := (tick_record_rel S.C S.P S.X _ _).of_outcome hrun
        have hΛ := (GoldilocksCorrectness.Proofs.Executions.tickInputState_record x i t v).1
        have hvv : (tickInputState x i t v).v = v :=
          (tickInputState_record x i t v).2.trans (lem11_node_invariant S Sched x i v).2.1
        rcases hrel b hb with hb' | ⟨a, ha, hab, hav⟩
        · rw [hΛ] at hb'
          exact lift (ih b hb')
        · have hsent := step_sent_of_tick_send hl hmem hrun ha
          exact ⟨i, t, a, by omega, hl, (Finset.mem_sdiff.1 hmem).1,
            (Finset.mem_sdiff.1 hmem).2, hsent, by rw [hav, hvv], hab,
            tick_attestation_well_formed S Sched x i t v a hl hsent⟩
      · rw [h] at hb
        have hΛ : (Goldilocks.Sts.receive S.C S.P S.X x[i][v].st sm.msg).Λ = (x[i][v].st).Λ := by
          cases sm.msg with
          | block B =>
              show (on_block S.C S.P S.X _ B).Λ = _
              rw [on_block_eq]
              split <;> rfl
          | gfVote vote =>
              show (on_ac_message _ _ _ vote).Λ = _
              rw [on_ac_message_eq]
          | attest a => exact GoldilocksCorrectness.Proofs.Routines.on_attestation_Λ _ _
        rw [hΛ] at hb
        exact lift (ih b hb)

/-- **Kit fact, a content of an honest record was sent by its own tick.** Every content of `v`'s
anti-slashing record before `t` is the content of an attestation of `v`, well formed, that `v` put
on the wire at its tick at a time `t' < t`, awake and honest then.

Why: `record_content_sent_step` at the step `stepBefore x t`, whose earlier steps end before `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `b`: the content.

Read aloud: every content of a validator's record is the content of a well-formed attestation of
that validator, put on the wire by its own tick, awake and honest then. -/
theorem record_content_sent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (b : AttestationContent)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- `b` is a content of `v`'s record before `t`
    (hb : b ∈ (stateBefore x t v).Λ.sent) :
    ∃ (j t' : ℕ) (a : Attestation V), x.lbl j = AtomicAction.tickAllAwake t' ∧ t' < t ∧
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent ∧
      a.val_index = v ∧ a.content = b ∧ attestation_well_formed a = true := by
  obtain ⟨j, t', a, hj, hl, h⟩ := record_content_sent_step S Sched x v (stepBefore x t) b hb
  have hlt : x[j + 1].time < t := (lt_stepBefore_iff x hDiv).1 hj
  rw [(time_of_lbl_tickAllAwake x hl).2] at hlt
  exact ⟨j, t', a, hl, hlt, h⟩

/-! ## A block held early is in the voter tree and a viable head -/

/-- **Kit fact, a block held early is in the voter tree and a viable head.** When `w` holds `B`
before a time `t₀` that is at most the view freeze of slot `s' − 1` and at most the vote time of
slot `s'`, `w`'s frame before that vote time has the root `ρ` and `head_height_floor` equal to `φ`, `ρ` is `B` or an
ancestor of `B`, and `B`'s chain-state height is at least `φ`: then `B` is in `w`'s voter tree of
slot `s'` and is a viable head of `w`'s frame then.

Why: `B` stays in `w`'s tree with its stamp, which is before `t₀` (`blockStamp_before`), so before
the view freeze; the finalized block is `ρ` or an ancestor of it (Lemma 46), so `B` is in the
frame's tree, and Lemma 56 makes it a viable head, its chain state being its own (Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time `w` holds `B` by;
- `s'`: the slot of the vote; `w`: the voter; `B`: the block; `ρ`, `φ`: the root and `head_height_floor` of
  `w`'s frame; `tree`: `w`'s voter tree.

Read aloud: a block a voter held before the view freeze, on its root's chain and at its `head_height_floor`, is
in its voter tree and is a viable head. -/
theorem proposal_viable_head_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ s' : ℕ) (w : V) (B ρ : Block V) (φ : Height)
    (tree : Finset (Block V))
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- `w` holds `B` before `t₀`
    (hBin : B ∈ (stateBefore x t₀ w).S.T)
    -- `t₀` is at most the view freeze of slot `s' − 1`, and at most the vote time of slot `s'`
    (ht₀ : t₀ ≤ viewFreeze S (s' - 1))
    (ht₀' : t₀ ≤ voteTime S s')
    -- `w`'s frame before the vote time of slot `s'` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape (stateBefore x (voteTime S s') w).S ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRoot : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hφ : φ ≤ (chainStateOf S.C B).h)
    -- `tree` is `w`'s voter tree of slot `s'`
    (htree : voter_block_tree S.C (stateBefore x (voteTime S s') w).A
      (fg_to_ac (stateBefore x (voteTime S s') w).S) s' = .ok tree) :
    B ∈ tree ∧ B ∈ (fg_to_ac (stateBefore x (voteTime S s') w).S).viable_heads := by
  have hG := stateBefore_grows x hDiv w ht₀'
  have hT : B ∈ (stateBefore x (voteTime S s') w).S.T := hG.1 hBin
  have hFρ : (stateBefore x (voteTime S s') w).S.F.AncestorEq ρ := by
    rw [← hShape.1]
    exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ w
  have hFB := ancestorEq_trans hFρ hRoot
  have hΦ : B ∈ (fg_to_ac (stateBefore x (voteTime S s') w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hT, hFB⟩
  obtain ⟨st, hst, hlt⟩ := blockStamp_before hDiv hBin
  have hkept : (stateBefore x (voteTime S s') w).A.timestamp_block B =
      (stateBefore x t₀ w).A.timestamp_block B := hG.2.2.2.1 B hBin
  have hle : ((((t₀ : ℕ) : Int)) : Stamp) ≤ ((S.C.t_ (s' - 1) + 3 * S.C.Δ : Time) : Stamp) := by
    rw [← viewFreeze_cast]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast ht₀)
  have hσ : (stateBefore x (voteTime S s') w).S.σ B = chainStateOf S.C B :=
    (lem11_node_invariant S Sched x (stepBefore x (voteTime S s')) w).1.2.2.2.2.2.1 B hT
  refine ⟨(GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _ s' tree
    htree B).2 ⟨hΦ, st, by rw [hkept]; exact hst, Or.inl (lt_of_lt_of_le hlt hle)⟩, ?_⟩
  refine ((GoldilocksCorrectness.Statements.Routines.lem56_frame_of_shape _ _ _ hShape).2.2 B).2
    ⟨hT, hFB, hRoot, ?_⟩
  rw [hσ]
  exact hφ

/-! ## A proposer's anchor is on its proposal's chain -/

/-- **Kit fact, the proposer's anchor is the parent of its proposal or an ancestor of it.** When
`q`'s tick at the start of slot `s''` is the step `i` and put `B'` on the wire, `q`'s anchor at that
start, on its state before it, is `B'`'s parent or an ancestor of it.

Why: `B'`'s parent is the end of `q`'s Goldfish fork choice from its anchor (Lemma 19), a walk
(`ghost`) that ends at its start or at a descendant of it (`ghost_spec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot; `i`: the step of
  `q`'s tick; `B'`: the block; `q`: the proposer.

Read aloud: the proposal's parent descends from the anchor its walk started from. -/
theorem get_anchor_ancestorEq_proposal_parent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s'' i : ℕ) (B' : Block V) (q : V)
    -- `q`'s tick at the start of slot `s''` is the step `i`, and put `B'` on the wire
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S s''))
    (hsent : (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    (get_anchor (stateBefore x (slotStart S s'') q).A
      (fg_to_ac (stateBefore x (slotStart S s'') q).S)
      ((slotStart S s'' : ℕ) : Int)).AncestorEq B'.parent := by
  have hi : stepBefore x (slotStart S s'') = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  have hAq : (tickInputState x i (slotStart S s'') q).A =
      (stateBefore x (slotStart S s'') q).A := by
    rw [(tickInputState_frame x i _ q).2.1]
    unfold stateBefore
    rw [hi]
  have hSq : (tickInputState x i (slotStart S s'') q).S =
      (stateBefore x (slotStart S s'') q).S := by
    rw [(tickInputState_frame x i _ q).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, H, votes, support, -, -, hWalk, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B'
      hrun₁ hB₁
  rw [hAq, hSq] at hWalk
  have hpar : B'.parent = H := by rw [hBdef]; rfl
  rw [hpar]
  rcases GoldilocksCorrectness.Proofs.Routines.ghost_spec
      ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | ⟨h, -⟩
  · rw [h]
    exact ancestorEq_refl _
  · exact h

/-! ## The live lock entries an honest update leaves -/

/-- **Kit fact, the live lock entries of an honest update are on its saved block's chain.** When
`v` is awake and honest from the duty window's start of slot `s + 1` to the support cutoff `a` of
slot `s + 1`; `v`'s confirmation update of slot `s + 1` at `a` answers `A'` saving `B` as the
confirmation of slot `s`; `B` is of slot `s`; and every lock entry `v`'s revocation of slot `s + 1`
leaves, live at the vote time of slot `s + 1`, is on a block compatible with `B` — then every lock
entry of `A'` live at `a` is on `B` or an ancestor of `B`.

Why: an entry the update adds is on its saved confirmation or an ancestor of it (Lemma 35). Any
other entry was held before `a`, so it is in the revocation's answer at the vote time of slot
`s + 1` (lock entries only shrink between the two duty times), live there, hence compatible with
`B`; and it is not on a strict descendant of `B`: it was added by an update of a slot `s₁ + 1` with
`s₁ < s` on a block of `v`'s tree then (Lemma 39), whose slot is at most `s₁ + 1 ≤ s`, while a
strict descendant of `B` has a slot greater than `B`'s.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of the confirmation;
- `B`: the saved block; `v`: the validator; `A'`: the update's answer.

Read aloud: right after an honest update that saves `B`, no live lock of the updater is past `B`
or off `B`'s chain. -/
theorem update_lock_entries_ancestorEq (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (v : V) (A' : ACState V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` answers `A'`
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    -- `A'` saves `B` as the confirmation of slot `s`
    (hSaved : A'.saved_confirmation s = some B)
    -- `B` is a block of slot `s`
    (hBslot : B.slot = s)
    -- the live entries `v`'s revocation of slot `s + 1` leaves are compatible with `B`
    (hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B := by
  intro e he hlive
  rcases (GoldilocksCorrectness.Statements.Routines.lem35_update_confirmation_lock_entries S.C
      S.P _ A' _ _ _ hUpdate).2 e he with hold | ⟨-, -, -, ⟨C', hC', hBC⟩, -⟩
  swap
  · rw [Nat.add_sub_cancel, hSaved] at hC'
    cases hC'
    exact hBC
  -- an entry held before the cutoff
  have he₂ : e ∈ (stateBefore x (supportCutoff S (s + 1)) v).A.lock_entries :=
    (Finset.mem_filter.1 hold).1
  have hdl : ((supportCutoff S (s + 1) : ℕ) : Int) < e.d := by
    rw [is_live_iff] at hlive
    exact hlive.1
  -- the times
  have hΔ := one_le_Δ S
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hslot : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      S.C.slot (t : Int) = s + 1 :=
    fun t h1 h2 => slot_eq_of_mem S (by omega) (by omega)
  have hslot₃ := hslot (voteTime S (s + 1)) le_rfl (by omega)
  -- the tick at the vote time of slot `s + 1` ran the revocation
  obtain ⟨hl₃, -, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s + 1))
  have hv₃a := hv (voteTime S (s + 1)) (by omega) (by omega)
  obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hv₃a.1 hv₃a.2
  have hAw₃ := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (voteTime S (s + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => (hv t h1 (by omega)).1) hv₃a.2
  have hA₃ : (tickInputState x (stepBefore x (voteTime S (s + 1))) (voteTime S (s + 1)) v).A =
      (stateBefore x (voteTime S (s + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₃ : (tickInputState x (stepBefore x (voteTime S (s + 1))) (voteTime S (s + 1)) v).S =
      (stateBefore x (voteTime S (s + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A'', hRevoke, hlock₃⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
      hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact hAw₃)
  rw [hslot₃, hA₃, hS₃] at hRevoke
  -- from the tick at the vote time to the cutoff the lock entries only shrink
  have hsub : (stateBefore x (supportCutoff S (s + 1)) v).A.lock_entries ⊆ A''.lock_entries := by
    rw [← hlock₃, ← hst₃]
    refine stateBefore_lock_entries_subset x hDiv v (by omega) (by omega) ?_
    intro t'' h1 h2
    rw [hti₃'] at h1
    rw [hslot t'' (by omega) (by omega), ← voteTime_cast, ← supportCutoff_cast]
    constructor <;> intro h <;> omega
  have heA'' := hsub he₂
  have hcompat : e.B.compatible B = true := by
    refine hLocks A'' hRevoke e heA'' ?_
    rw [is_live_iff]
    have h32 : ((voteTime S (s + 1) : ℕ) : Int) < ((supportCutoff S (s + 1) : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    exact ⟨lt_trans h32 hdl,
      GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s)
        hRevoke e heA''⟩
  rcases (compatible_iff _ _).1 hcompat with h | hBe
  · exact h
  -- `e`'s block is not a strict descendant of `B`: it was added at an earlier slot
  obtain ⟨s₁, -, hts, -, A₁, -, e₀, -, -, he₀T, -, -, -, htrace⟩ :=
    lem39_lock_entry_provenance S Sched x (supportCutoff S (s + 1)) v e hDiv he₂
  obtain ⟨e', -, -, hee', he'e₀⟩ := htrace (supportCutoff S (s + 1)) hts le_rfl
  have hee₀ := ancestorEq_trans hee' he'e₀
  have hs₁ : s₁ < s := by
    by_contra hns
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hns) with hlt | heq
    · have := supportCutoff_lt_of_lt S (by omega : s + 1 < s₁ + 1)
      omega
    · rw [heq] at hts
      exact lt_irrefl _ hts
  have he₀T' : e₀.B ∈ (stateBefore x (supportCutoff S (s₁ + 1)) v).S.T :=
    ((mem_fg_to_ac_tree _ _).1 he₀T).1
  have hslot₀ : e₀.B.slot ≤ s₁ + 1 := by
    have := slot_le_of_mem_T_before hDiv hMono he₀T'
    rw [(supportCutoff_slot S s₁).1] at this
    exact this
  have hBe₀ := ancestorEq_trans hBe hee₀
  by_cases hEq : B = e₀.B
  · rw [hEq]
    exact hee₀
  · have hTC : TreeClosed S.P S.X (stateBefore x (supportCutoff S (s₁ + 1)) v).S :=
      (lem11_node_invariant S Sched x (stepBefore x (supportCutoff S (s₁ + 1))) v).1.2.2.1
    have hlt := slot_lt_of_ancestorEq_of_treeClosed hTC he₀T' hBe₀ hEq
    have h2 : s < s₁ + 1 := by
      rw [← hBslot]
      exact lt_of_lt_of_le hlt hslot₀
    omega

end GoldilocksCorrectness.Proofs.Executions
