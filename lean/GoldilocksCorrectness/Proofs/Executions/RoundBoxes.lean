module
public import GoldilocksCorrectness.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Proofs.Executions.Boxes
public import GoldilocksCorrectness.Statements.Executions.HeightInvariantStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-! Each box
gives the frame shape at every member and every time of the window (Lemma 56's readers); the `head_height_floor` (the least chain-state height a viable block may have)
bound on the honest proposal is `proposal_viable`; the equal `h_max` of box 2 is Lemma 57's
justified height (`h_j_eq_of_boxTwo`), and its record hypothesis at `H = h_max − 1` is the bridge
`entry_block_of_boxTwo`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (floor_of_boxOne_or_boxThree)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes
  FrameShape BoxOne BoxTwo BoxThree frameShape_of_boxOne frameShape_of_boxTwo
  frameShape_of_boxThree lem56_frame_of_shape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- An honest proposal of slot `s` is at a slot `s ≥ 1`, its parent is an ancestor of it, and
`head_height_floor` at the proposer before the start of slot `s` is at most its chain-state height, when its parent
is in the proposer's viable tree: a tick proposes only at a slot after the first (Lemma 19), and
then `proposal_parent_walk_end` and `proposal_viable` apply.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `B`: the proposal;
  `p`: its proposer. -/
theorem proposal_facts_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) (p : V)
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in `p`'s viable tree
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree) :
    1 ≤ s ∧ B.parent.AncestorEq B ∧
      head_height_floor (stateBefore x (slotStart S s) p).S ≤ (chainStateOf S.C B).h := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have h1 : 1 ≤ s := by
    obtain ⟨-, n', sent, hrun, hB⟩ := tick_send_of_honestSendAt hl hsent
    have hpos := (GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n' _
      sent B hrun hB).1
    have hΔ := one_le_Δ S
    have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    rw [slot_eq_of_mem S (le_refl _) (by omega)] at hpos
    exact hpos
  have hsm : s - 1 + 1 = s := by omega
  have hl' : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s - 1 + 1)) := by rw [hsm]; exact hl
  obtain ⟨-, -, hpar, -⟩ := proposal_parent_walk_end S Sched x (s - 1) i B p hl' hsent
  have hv := proposal_viable S Sched x (s - 1) B p ⟨i, hl', hsent⟩ (by rw [hsm]; exact hParentIn)
  rw [hsm] at hv
  exact ⟨h1, ancestorEq_of_parent? hpar, hv⟩

/-- Lemma 80 in box 1, its hypotheses. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`. -/
theorem lem80_boxOne_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxOne (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    (hp : p ∈ Hon)
    (hs'' : supportCutoff S (s + 1) ≤ slotStart S s'')
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ - 1 ≤ (chainStateOf S.C W).h)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree) :
    (∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (stateBefore x t v).S.F (h₀ - 1)) ∧
    (∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true) ∧
    (∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ - 1 ≤ (chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h) := by
  have hΔ := one_le_Δ S
  have hc : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hv : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hShape : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (stateBefore x t v).S.F (h₀ - 1) := by
    intro v hv' t h1 h2
    have h := (frameShape_of_boxOne _ (hBox v hv' t h1 h2).1).2
    rw [(hBox v hv' t h1 h2).2] at h
    exact h
  -- the floor `h₀ − 1` is at most `H`
  have hfl : h₀ - 1 ≤ (chainStateOf S.C B).h := by
    have h := (proposal_facts_at S Sched x s B p hPropose hParentIn).2.2
    rw [(hShape p hp (slotStart S s) le_rfl (by omega)).2] at h
    exact h
  refine ⟨hShape, hFw, hFar, hFafter, hHeadP, fun v hv' => ?_⟩
  obtain ⟨hb, hmax⟩ := hBox v hv' (supportCutoff S (s + 1)) (by omega) hs''
  have hb' : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j + 1 <
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_max := hb
  rw [hmax] at hb'
  unfold Height at *
  omega

/-- Lemma 80 in box 2, its hypotheses. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`. -/
theorem lem80_boxTwo_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s s'' : ℕ) (Hon Q : Finset V) (X B J₀ : Block V) (p : V)
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxTwo (stateBefore x t v).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hp : p ∈ Hon)
    (hs'' : supportCutoff S (s + 1) ≤ slotStart S s'')
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    (hQ : Q ⊆ Hon)
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock
        ((stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1) = some T' → T' = J₀.root) :
    (∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S J₀ ((stateBefore x (slotStart S s) p).S.h_max - 1)) ∧
    J₀.AncestorEq B.parent ∧ J₀.AncestorEq B ∧ J₀.compatible B = true ∧
    (∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
    (∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) := by
  have hΔ := one_le_Δ S
  have hc : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hv : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hBoxP := hBox p hp (slotStart S s) le_rfl (by omega)
  -- every `h_max` of the window is `J₀`'s height plus one, `p`'s at the start of slot `s`
  have hmax : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.h_max = (stateBefore x (slotStart S s) p).S.h_max := by
    intro v hv' t h1 h2
    have hB := hBox v hv' t h1 h2
    rw [hB.1, hBoxP.1, h_j_eq_of_boxTwo S Sched x _ v J₀ hB hJ₀,
      h_j_eq_of_boxTwo S Sched x _ p J₀ hBoxP hJ₀]
  have hShape : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S J₀ ((stateBefore x (slotStart S s) p).S.h_max - 1) := by
    intro v hv' t h1 h2
    have h := frameShape_of_boxTwo _ _ (hBox v hv' t h1 h2)
    rw [hmax v hv' t h1 h2] at h
    exact h
  -- the root `J₀` is an ancestor of `B`'s parent, which is in `p`'s viable tree
  obtain ⟨-, hPB, hfl⟩ := proposal_facts_at S Sched x s B p hPropose hParentIn
  have hJP : J₀.AncestorEq B.parent := by
    have hR := (lem56_frame_of_shape _ _ _ (hShape p hp (slotStart S s) le_rfl (by omega))).1
    have hP := hParentIn
    rw [mem_viable_tree_iff] at hP
    obtain ⟨-, hRB, -⟩ := hP
    rw [hR] at hRB
    exact hRB
  have hJB := ancestorEq_trans hJP hPB
  rw [(hShape p hp (slotStart S s) le_rfl (by omega)).2] at hfl
  refine ⟨hShape, hJP, hJB, (compatible_iff _ _).2 (Or.inl hJB), hHeadP, fun v hvQ => ?_⟩
  -- the record: the cache `h_j` is `h_max − 1`, at most `H`; at `H = h_max − 1`, the lock is `T`
  have hvH := hQ hvQ
  have hBv := hBox v hvH (supportCutoff S (s + 1)) (by omega) hs''
  have hmv := hmax v hvH (supportCutoff S (s + 1)) (by omega) hs''
  have hjv : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max =
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j + 1 := hBv.1
  by_cases hlt : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h
  · exact Or.inl hlt
  · have hH : (chainStateOf S.C B).h =
        (stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1 := by
      unfold Height at *
      omega
    right
    cases hl : (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h with
    | none => exact Or.inl rfl
    | some T' =>
        right
        have hTT : T' = J₀.root := hLockJ₀ v hvQ T' (by rw [← hH]; exact hl)
        have hE := entry_block_of_boxTwo S Sched x _ v B J₀ hBv hJ₀ hJB hH
        rw [hTT, hE]

/-- Lemma 80 in box 3, its hypotheses. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`. -/
theorem lem80_boxThree_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxThree (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    (hp : p ∈ Hon)
    (hs'' : supportCutoff S (s + 1) ≤ slotStart S s'')
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ ≤ (chainStateOf S.C W).h)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree) :
    (∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (stateBefore x t v).S.F h₀) ∧
    (∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true) ∧
    (∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ ≤ (chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h) := by
  have hΔ := one_le_Δ S
  have hc : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hv : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hShape : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (stateBefore x t v).S.F h₀ := by
    intro v hv' t h1 h2
    have h := (frameShape_of_boxThree _ (hBox v hv' t h1 h2).1).2
    rw [(hBox v hv' t h1 h2).2] at h
    exact h
  -- the floor `h₀` is at most `H`
  have hfl : h₀ ≤ (chainStateOf S.C B).h := by
    have h := (proposal_facts_at S Sched x s B p hPropose hParentIn).2.2
    rw [(hShape p hp (slotStart S s) le_rfl (by omega)).2] at h
    exact h
  refine ⟨hShape, hFw, hFar, hFafter, hHeadP, fun v hv' => ?_⟩
  obtain ⟨hb, hmax⟩ := hBox v hv' (supportCutoff S (s + 1)) (by omega) hs''
  have hj := (frameShape_of_boxThree _ hb).1
  rw [hmax] at hj
  unfold Height at *
  omega

/-- Lemma 80 in box 1. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads Lemma 80
(`lem80_round_height_advances_frame`) at the same slots, whose bound is that time. -/
theorem lem80_boxOne (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    (hGST : GST ≤ voteTime S (s - 1))
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxOne (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ - 1 ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  obtain ⟨hShape, hRootW, hRootAr, hRootAfter, hHeadP', hjlt⟩ :=
    lem80_boxOne_hypotheses S Sched x s s'' Hon X B p h₀ hBox hFw hFar hFafter hp
      (le_trans (Nat.le_add_right _ _) hs'') hHeadP hPropose hParentIn
  exact lem80_round_height_advances_frame S Sched x GST r s s'' Hon Q Hs H X B B' p q (h₀ - 1)
    (fun v t => (stateBefore x t v).S.F) hDiv hMono hSync hCatch hRoots hParent hOwner
    hSyncF hCatchF hs hs1 hs'' hGST hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly
    hRootNew hHs hVoters hVotersQ hHalf hShape hRootW hRootAr hRootAfter hHeadP' hParentIn hQ
    hQuorum (fun v hv => Or.inl (hjlt v (hQ hv))) hq hPropose'

/-- Lemma 80 in box 2. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads Lemma 80
(`lem80_round_height_advances_frame`) at the same slots, whose bound is that time. -/
theorem lem80_boxTwo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' J₀ : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    (hGST : GST ≤ voteTime S (s - 1))
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxTwo (stateBefore x t v).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock
        ((stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1) = some T' → T' = J₀.root)
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  obtain ⟨hShape, hJP, hJB, hJc, hHeadP', hRecord⟩ :=
    lem80_boxTwo_hypotheses S Sched x s s'' Hon Q X B J₀ p hBox hJ₀ hp
      (le_trans (Nat.le_add_right _ _) hs'') hHeadP hPropose hParentIn hQ hLockJ₀
  exact lem80_round_height_advances_frame S Sched x GST r s s'' Hon Q Hs H X B B' p q
    ((stateBefore x (slotStart S s) p).S.h_max - 1) (fun _ _ => J₀) hDiv hMono hSync hCatch
    hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHon hp hPropose hHsPrev
    hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hShape (fun _ _ => hJP)
    (fun _ _ => hJB) (fun _ _ _ _ _ => hJc) hHeadP' hParentIn hQ hQuorum hRecord hq hPropose'

/-- Lemma 80 in box 3. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads Lemma 80
(`lem80_round_height_advances_frame`) at the same slots, whose bound is that time. -/
theorem lem80_boxThree (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    (hGST : GST ≤ voteTime S (s - 1))
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxThree (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  obtain ⟨hShape, hRootW, hRootAr, hRootAfter, hHeadP', hjlt⟩ :=
    lem80_boxThree_hypotheses S Sched x s s'' Hon X B p h₀ hBox hFw hFar hFafter hp
      (le_trans (Nat.le_add_right _ _) hs'') hHeadP hPropose hParentIn
  exact lem80_round_height_advances_frame S Sched x GST r s s'' Hon Q Hs H X B B' p q h₀
    (fun v t => (stateBefore x t v).S.F) hDiv hMono hSync hCatch hRoots hParent hOwner
    hSyncF hCatchF hs hs1 hs'' hGST hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly
    hRootNew hHs hVoters hVotersQ hHalf hShape hRootW hRootAr hRootAfter hHeadP' hParentIn hQ
    hQuorum (fun v hv => Or.inl (hjlt v (hQ hv))) hq hPropose'

/-! ## `lem80wq_round_height_advances_steps` in the three boxes -/

/-- `lem80wq_round_height_advances_steps` in box 1. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxOne (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 1 before the start of slot `s`
    (hBoxP : BoxOne (stateBefore x (slotStart S s) p).S)
    -- before the vote time of slot `s`, every member of `Hon s` is in box 1 with `h_max` at least
    -- `p`'s and at most `h(B.parent) + 1`, or in box 3 with `h_max` at least `p`'s minus one and at
    -- most `h(B.parent)`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxOne (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h + 1) ∨
      (BoxThree (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max + 1 ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h))
    -- before the action time, every member of `Hon s` is in box 1 with `h_max` at most `h(B) + 1`,
    -- or in box 3 with `h_max` at most `h(B)`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxOne (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h + 1) ∨
      (BoxThree (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- `h_max − 1`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  have hpS := frameShape_of_boxOne _ hBoxP
  -- the members' frames: the root is the finalized block, the `head_height_floor` is between
  -- the proposer's and the parent's height before the vote time, at most `h(B)` before `a`
  have hW : ∀ w ∈ Hon s, get_fc_root (stateBefore x (voteTime S s) w).S = (stateBefore x (voteTime S s) w).S.F ∧
      head_height_floor (stateBefore x (slotStart S s) p).S ≤ head_height_floor (stateBefore x (voteTime S s) w).S ∧
      head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C B.parent).h ∧
      (stateBefore x (voteTime S s) w).S.h_j < (chainStateOf S.C B.parent).h := by
    intro w hw
    rw [hpS.2.2]
    refine floor_of_boxOne_or_boxThree _ _ _ ?_
    rcases hBoxW w hw with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
    · have hb' : (stateBefore x (voteTime S s) w).S.h_j + 1 < (stateBefore x (voteTime S s) w).S.h_max := hb
      exact Or.inl ⟨hb, by unfold Height at *; omega, h2⟩
    · exact Or.inr ⟨hb, by unfold Height at *; omega, h2⟩
  have hV : ∀ v ∈ Hon s, get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S = (stateBefore x (supportCutoff S (s + 1)) v).S.F ∧
      0 ≤ head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ∧
      head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ≤ (chainStateOf S.C B).h ∧
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h := by
    intro v hv
    refine floor_of_boxOne_or_boxThree _ _ _ ?_
    rcases hBoxV v hv with ⟨hb, h2⟩ | ⟨hb, h2⟩
    · exact Or.inl ⟨hb, Nat.zero_le _, h2⟩
    · exact Or.inr ⟨hb, Nat.zero_le _, h2⟩
  refine lem80wq_round_height_advances_steps S Sched x GST r s s'' Hon Q Hs H X B B' p q
    (head_height_floor (stateBefore x (slotStart S s) p).S) (fun w => head_height_floor (stateBefore x (voteTime S s) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S) (get_fc_root (stateBefore x (slotStart S s) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S s) w).S) (fun v => get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S)
    hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHonMono
    hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    (fun w hw => ⟨(hW w hw).2.1, (hW w hw).2.2.1⟩) (fun v hv => (hV v hv).2.2.1)
    (fun w hw => by rw [(hW w hw).1]; exact hFw w hw)
    (fun v hv => by rw [(hV v hv).1]; exact hFar v hv)
    (by rw [hpS.2.1, hpS.2.2]; exact hHeadP) hStep hStepLast hQ hQuorum
    (fun v hv => Or.inl (hV v (hQ hv)).2.2.2) hq hFrameQ hPropose'

/-- `lem80wq_round_height_advances_steps` in box 2. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' J₀ : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `J₀` is not the genesis block; `p` is in box 2 with `J₀` before the start of slot `s`, and
    -- every member of `Hon s` is too before the vote time of slot `s` and before the action time
    (hJ₀ : J₀ ≠ Block.genesis)
    (hBoxP : BoxTwo (stateBefore x (slotStart S s) p).S J₀)
    (hBoxW : ∀ w ∈ Hon s, BoxTwo (stateBefore x (voteTime S s) w).S J₀)
    (hBoxV : ∀ v ∈ Hon s, BoxTwo (stateBefore x (supportCutoff S (s + 1)) v).S J₀)
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s `h_max − 1`; and `B`'s
    -- parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    -- unforgeability, and fewer than a third of the validators corrupted up to the action time
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) ((supportCutoff S (s + 1) : ℕ) : Int))
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hΔ := one_le_Δ S
  -- every `head_height_floor` read is `J₀`'s height: `h_max − 1 = h_j` in box 2 (Lemma 57)
  have hP := frameShape_of_boxTwo _ _ hBoxP
  have hjP := h_j_eq_of_boxTwo S Sched x _ p J₀ hBoxP hJ₀
  have hfP : head_height_floor (stateBefore x (slotStart S s) p).S = (chainStateOf S.C J₀).h := by
    rw [hP.2, hBoxP.1, Nat.add_sub_cancel, hjP]
  have hfl : ∀ (t : ℕ) (v : V), BoxTwo (stateBefore x t v).S J₀ →
      get_fc_root (stateBefore x t v).S = J₀ ∧
      head_height_floor (stateBefore x t v).S = (chainStateOf S.C J₀).h := by
    intro t v hb
    have h := frameShape_of_boxTwo _ _ hb
    refine ⟨h.1, ?_⟩
    rw [h.2, hb.1, Nat.add_sub_cancel, h_j_eq_of_boxTwo S Sched x _ v J₀ hb hJ₀]
  -- `J₀` is an ancestor of `B`'s parent, which is in `p`'s viable tree; the floor is at most the
  -- parent's height
  obtain ⟨hs1', hPB, -⟩ := proposal_facts_at S Sched x s B p hPropose hParentIn
  have hJP : J₀.AncestorEq B.parent := by
    have hPin := hParentIn
    rw [mem_viable_tree_iff] at hPin
    obtain ⟨-, hRB, -⟩ := hPin
    rw [(lem56_frame_of_shape _ _ _ hP).1] at hRB
    exact hRB
  have hJB := ancestorEq_trans hJP hPB
  have hsm : s - 1 + 1 = s := by omega
  have hφ : (chainStateOf S.C J₀).h ≤ (chainStateOf S.C B.parent).h := by
    have h := proposal_parent_viable S Sched x (s - 1) B p (by rw [hsm]; exact hPropose)
      (by rw [hsm]; exact hParentIn)
    rw [hsm, hfP] at h
    exact h
  have hPBh := (lem47_chain_state_heights S.C B.parent B).2.2.2.1 hPB
  refine lem80wq_round_height_advances_steps S Sched x GST r s s'' Hon Q Hs H X B B' p q
    (head_height_floor (stateBefore x (slotStart S s) p).S) (fun w => head_height_floor (stateBefore x (voteTime S s) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S) (get_fc_root (stateBefore x (slotStart S s) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S s) w).S) (fun v => get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S)
    hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHonMono
    hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    (fun w hw => by rw [(hfl _ w (hBoxW w hw)).2, hfP]; exact ⟨le_rfl, hφ⟩)
    (fun v hv => by rw [(hfl _ v (hBoxV v hv)).2]; exact le_trans hφ hPBh)
    (fun w hw => by rw [(hfl _ w (hBoxW w hw)).1]; exact hJP)
    (fun v hv => by rw [(hfl _ v (hBoxV v hv)).1]; exact hJB)
    (by rw [hP.1, hP.2]; exact hHeadP) hStep hStepLast hQ hQuorum (fun v hvQ => ?_) hq hFrameQ
    hPropose'
  -- the record: `h_j = h(J₀)`; at `H = h_max − 1` the lock, when set, is on `J₀` (one
  -- justification per height), which is `B`'s `T_h`
  have hBv := hBoxV v (hQ hvQ)
  have hjv := h_j_eq_of_boxTwo S Sched x _ v J₀ hBv hJ₀
  by_cases hlt : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h
  · exact Or.inl hlt
  · have hH : (chainStateOf S.C B).h = (stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1 := by
      rw [hBv.1, Nat.add_sub_cancel]
      unfold Height at *
      omega
    right
    cases hl : (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h with
    | none => exact Or.inl rfl
    | some T' =>
        right
        have hTT : T' = J₀.root := lockBox_of_one_justification S Sched x hU _ v v J₀ T' hAdv hBv
          (by rw [← hH]; exact hl)
        have hE := entry_block_of_boxTwo S Sched x _ v B J₀ hBv hJ₀ hJB hH
        rw [hTT, hE]

/-- `lem80wq_round_height_advances_steps` in box 3. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxThree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 3 before the start of slot `s`
    (hBoxP : BoxThree (stateBefore x (slotStart S s) p).S)
    -- before the vote time of slot `s`, every member of `Hon s` is in box 3 with `h_max` at least
    -- `p`'s and at most `h(B.parent)`, or in box 1 with `h_max` at least `p`'s plus one and at most
    -- `h(B.parent) + 1`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxThree (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h) ∨
      (BoxOne (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max + 1 ≤ (stateBefore x (voteTime S s) w).S.h_max ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h + 1))
    -- before the action time, every member of `Hon s` is in box 3 with `h_max` at most `h(B)`, or
    -- in box 1 with `h_max` at most `h(B) + 1`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxThree (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h) ∨
      (BoxOne (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h + 1))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- `h_max`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  have hpS := frameShape_of_boxThree _ hBoxP
  -- the members' frames: the root is the finalized block, the `head_height_floor` is between
  -- the proposer's and the parent's height before the vote time, at most `h(B)` before `a`
  have hW : ∀ w ∈ Hon s, get_fc_root (stateBefore x (voteTime S s) w).S = (stateBefore x (voteTime S s) w).S.F ∧
      head_height_floor (stateBefore x (slotStart S s) p).S ≤ head_height_floor (stateBefore x (voteTime S s) w).S ∧
      head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C B.parent).h ∧
      (stateBefore x (voteTime S s) w).S.h_j < (chainStateOf S.C B.parent).h := by
    intro w hw
    rw [hpS.2.2]
    refine floor_of_boxOne_or_boxThree _ _ _ ?_
    rcases hBoxW w hw with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
    · exact Or.inr ⟨hb, h1, h2⟩
    · exact Or.inl ⟨hb, by unfold Height at *; omega, h2⟩
  have hV : ∀ v ∈ Hon s, get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S = (stateBefore x (supportCutoff S (s + 1)) v).S.F ∧
      0 ≤ head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ∧
      head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ≤ (chainStateOf S.C B).h ∧
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h := by
    intro v hv
    refine floor_of_boxOne_or_boxThree _ _ _ ?_
    rcases hBoxV v hv with ⟨hb, h2⟩ | ⟨hb, h2⟩
    · exact Or.inr ⟨hb, Nat.zero_le _, h2⟩
    · exact Or.inl ⟨hb, Nat.zero_le _, h2⟩
  refine lem80wq_round_height_advances_steps S Sched x GST r s s'' Hon Q Hs H X B B' p q
    (head_height_floor (stateBefore x (slotStart S s) p).S) (fun w => head_height_floor (stateBefore x (voteTime S s) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S) (get_fc_root (stateBefore x (slotStart S s) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S s) w).S) (fun v => get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S)
    hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHonMono
    hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    (fun w hw => ⟨(hW w hw).2.1, (hW w hw).2.2.1⟩) (fun v hv => (hV v hv).2.2.1)
    (fun w hw => by rw [(hW w hw).1]; exact hFw w hw)
    (fun v hv => by rw [(hV v hv).1]; exact hFar v hv)
    (by rw [hpS.2.1, hpS.2.2]; exact hHeadP) hStep hStepLast hQ hQuorum
    (fun v hv => Or.inl (hV v (hQ hv)).2.2.2) hq hFrameQ hPropose'

end GoldilocksCorrectness.Proofs.Executions
