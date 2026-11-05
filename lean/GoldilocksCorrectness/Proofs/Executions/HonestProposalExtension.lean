module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Handover
public import GoldilocksCorrectness.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# An honest proposal strictly extends the earlier outputs: the proofs

The new conclusions of Lemma 90 and Lemma 98,
each derived from the conclusions those lemmas already had:

- `confirmedExtendedByHonestProposalsBetween_unfold`, `confirmedExtendedByHonestProposals_unfold`,
  `finalizedExtendedByHonestProposalsBetween_unfold`: the three definitions read on the execution's
  node states, a proposal as `ProposalAt`;
- `confirmedOf_mem_tree`: a node state's confirmed tip is in its FG state's tree when its finalized
  block is;
- `slot_lt_of_ancestorEq_held_before`: a block that is a block held after a step at a time before
  the start of slot `s`, or an ancestor of one, has a slot less than `s`;
- `confirmedExtendedBetween_of_agree_included`, `confirmedExtended_of_agree_included`: Lemma 90's
  fourth conclusion from its agreement and its inclusion, read up to a time and with no upper end;
- `finalizedExtendedByHonestProposalsBetweenEveryReader_unfold`: the same reading of
  `FinalizedExtendedByHonestProposalsBetweenEveryReader`, the form with every reader up to a time
;
- `finalizedExtendedBetween_of_compatible_included`: Lemma 98's second conclusion from Lemma 86's
  compatibility of the finalized blocks and Lemma 98's first conclusion, both with every reader up
  to a time (the `EveryReader` forms).

The argument, both times: the proposal `B` of slot `s` has the slot `s`; every block a validator
holds before the start of slot `s`, and every ancestor of one, has a slot less than `s`; so an
output held before slot `s` is never `B` or a descendant of `B`, and the compatibility each lemma
gives leaves only the other order.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart confirmedOf ac_confirmed_cases)
open GoldilocksCorrectness.Proofs.Routines (slotStart_eq slotStart_mono supportCutoff_eq
  voteTime_eq slot_mono slot_mono_int slot_lt_of_lt_slotStart mem_fg_to_ac_tree fg_to_ac_F
  slot_lt_of_ancestorEq_of_treeClosed compatible_iff ancestorEq_trans ancestorEq_refl)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.View

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The definitions read on the execution -/

section Unfold

variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- `ConfirmedExtendedByHonestProposalsBetween S Sched x tE t` read on the execution: the proposal
as `ProposalAt`, the confirmed tips as `confirmedOf` of the node states.

Why: a proposal on the view is `ProposalAt` (`proposalAtV_iff`); the rest is the view form's.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: Lemma 90's fourth conclusion from `tE` and up to `t`, read on the node states. -/
theorem confirmedExtendedByHonestProposalsBetween_unfold (tE t : ℕ) :
    ConfirmedExtendedByHonestProposalsBetween S Sched x tE t ↔
      ∀ s : ℕ, tE ≤ slotStart S s → supportCutoff S (s + 1) ≤ t → HonestOpenerAt S Sched s →
        ∀ B : Block V, ProposalAt S Sched x s B →
          RootCollisionAtProposal S Sched x s B ∨
          ∀ (v : V) (i : ℕ), HonestThrough x i v → tE ≤ x[i].time → x[i].time < slotStart S s →
            (confirmedOf (x[i][v].st)).AncestorEq B ∧ confirmedOf (x[i][v].st) ≠ B :=
  forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => forall_congr' fun b =>
      imp_congr (GoldilocksCorrectness.Proofs.View.proposalAtV_iff x s b) Iff.rfl

/-- `ConfirmedExtendedByHonestProposals S Sched x tE` read on the execution, as
`confirmedExtendedByHonestProposalsBetween_unfold` with no upper end.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: Lemma 90's fourth conclusion from `tE`, read on the node states. -/
theorem confirmedExtendedByHonestProposals_unfold (tE : ℕ) :
    ConfirmedExtendedByHonestProposals S Sched x tE ↔
      ∀ s : ℕ, tE ≤ slotStart S s → HonestOpenerAt S Sched s →
        ∀ B : Block V, ProposalAt S Sched x s B →
          RootCollisionAtProposal S Sched x s B ∨
          ∀ (v : V) (i : ℕ), HonestThrough x i v → tE ≤ x[i].time → x[i].time < slotStart S s →
            (confirmedOf (x[i][v].st)).AncestorEq B ∧ confirmedOf (x[i][v].st) ≠ B :=
  forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ =>
    forall_congr' fun b =>
      imp_congr (GoldilocksCorrectness.Proofs.View.proposalAtV_iff x s b) Iff.rfl

/-- `FinalizedExtendedByHonestProposalsBetween S Sched x tE t` read on the execution: the proposal
as `ProposalAt`, the finalized blocks as the FG states'.

Why: a proposal on the view is `ProposalAt` (`proposalAtV_iff`); the rest is the view form's.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: Lemma 98's second conclusion from `tE` and up to `t`, read on the node states. -/
theorem finalizedExtendedByHonestProposalsBetween_unfold (tE t : ℕ) :
    FinalizedExtendedByHonestProposalsBetween S Sched x (Δ S) tE t ↔
      ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
        FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R + 1) ≤ t →
        ∀ B : Block V, ProposalAt S Sched x s B →
          RootCollisionAtProposal S Sched x s B ∨
          RootCollisionAtOpening S Sched x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), HonestThrough x j v →
            (∃ s' : ℕ, x[j].time ≤ supportCutoff S s' ∧ supportCutoff S s' ≤ t) →
            AwakeForDelayWithin S Sched (Δ S) v (slotStart S ((r + 3) * S.C.R)) x[j].time →
            ∀ (w : V) (i : ℕ), HonestThrough x i w → tE ≤ x[i].time →
              x[i].time < slotStart S s →
              (x[i][w].st).S.F.AncestorEq (x[j][v].st).S.F ∧
                (x[i][w].st).S.F ≠ (x[j][v].st).S.F :=
  forall₂_congr fun s _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
      forall_congr' fun b =>
        imp_congr (GoldilocksCorrectness.Proofs.View.proposalAtV_iff x s b) Iff.rfl

/-- `FinalizedExtendedByHonestProposalsBetweenEveryReader S Sched x tE t` read on the execution:
the proposal as `ProposalAt`, the finalized blocks as the FG states'.

Why: a proposal on the view is `ProposalAt` (`proposalAtV_iff`); the rest is the view form's.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: Lemma 98's second conclusion from `tE` and up to `t`, with every reader up to `t`,
read on the node states. -/
theorem finalizedExtendedByHonestProposalsBetweenEveryReader_unfold (tE t : ℕ) :
    FinalizedExtendedByHonestProposalsBetweenEveryReader S Sched x (Δ S) tE t ↔
      ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
        FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R) ≤ t →
        ∀ B : Block V, ProposalAt S Sched x s B →
          RootCollisionAtProposal S Sched x s B ∨
          RootCollisionAtOpening S Sched x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), HonestThrough x j v → x[j].time ≤ t →
            AwakeForDelayWithin S Sched (Δ S) v (slotStart S ((r + 3) * S.C.R)) x[j].time →
            ∀ (w : V) (i : ℕ), HonestThrough x i w → tE ≤ x[i].time →
              x[i].time < slotStart S s →
              (x[i][w].st).S.F.AncestorEq (x[j][v].st).S.F ∧
                (x[i][w].st).S.F ≠ (x[j][v].st).S.F :=
  forall₂_congr fun s _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
      forall_congr' fun b =>
        imp_congr (GoldilocksCorrectness.Proofs.View.proposalAtV_iff x s b) Iff.rfl

end Unfold

/-! ## Two kit facts on held blocks -/

omit [Fintype V] [RootOrder] in
/-- **Kit fact, the confirmed tip is held.** A node state's confirmed tip (`confirmedOf`) is in its
FG state's tree when its finalized block is.

Why: the confirmed tip is the record `n.A.latest_confirmed` when the record is in the tree of the
frame `fg_to_ac n.S`, whose blocks are blocks of `n.S.T`; and it is the finalized block otherwise.

The variables:
- `n`: the node state. -/
theorem confirmedOf_mem_tree (n : NodeState V)
    -- the finalized block is in the tree
    (hFT : n.S.F ∈ n.S.T) :
    confirmedOf n ∈ n.S.T := by
  unfold confirmedOf
  rcases ac_confirmed_cases n.A (fg_to_ac n.S) with ⟨hin, h⟩ | ⟨-, h⟩
  · rw [h]
    exact ((mem_fg_to_ac_tree n.S _).1 hin).1
  · rw [h, fg_to_ac_F]
    exact hFT

/-- **Kit fact, what is held before a slot starts has an earlier slot.** A block `B` that is a
block `D` of `u`'s tree after a step `i` at a time before the start of slot `s`, or an ancestor of
`D`, has a slot less than `s`.

Why: `D` is the genesis block, of slot `0`, or `u` put it on the wire at a step before `i` with its
clock then in a slot at least `D`'s (`tree_block_relayed`), a slot less than `s` since the clock
never passes the execution's time; a strict ancestor of `D` in the tree has a smaller slot
(`slot_lt_of_ancestorEq_of_treeClosed`).

The variables:
- `x`: the execution; `i`: the step; `u`: the validator; `s`: the slot; `B`, `D`: the blocks.

Read aloud: a block held before slot `s` starts, and each of its ancestors, is from a slot before
`s`. -/
theorem slot_lt_of_ancestorEq_held_before {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) {i : ℕ} {u : V} {s : ℕ} {B D : Block V}
    -- `u` holds `D` after step `i`
    (hD : D ∈ (x[i][u].st).S.T)
    -- `B` is `D` or an ancestor of it
    (hBD : B.AncestorEq D)
    -- step `i` is at a time before the start of slot `s`
    (ht : x[i].time < slotStart S s) :
    B.slot < s := by
  have hInv := (lem11_node_invariant S Sched x i u).1
  have h3 := slot_lt_of_lt_slotStart S ht
  have hDs : D.slot < s := by
    by_cases hg : D = Block.genesis
    · subst hg
      simp only [Block.slot]
      omega_nat
    obtain ⟨i'', hi'', -, -, hsl⟩ := tree_block_relayed x hD hg
    have h1 := slot_mono_int S (clock_le_time x (i'' + 1) u)
    have h2 := slot_mono S (time_mono x (show i'' + 1 ≤ i by omega))
    omega_nat
  by_cases hBD' : B = D
  · rw [hBD']
    exact hDs
  · exact lt_trans (slot_lt_of_ancestorEq_of_treeClosed hInv.2.2.1 hD hBD hBD') hDs

/-! ## Lemma 90's fourth conclusion -/

/-- **Lemma 90's fourth conclusion, read up to `t`, from its agreement and its inclusion.** When
every slot starting at or after `tE` is at least `2`, the agreement of the confirmed tips from `tE`
up to `t` (`ConfirmedAgreeBetween`) and the inclusion of the honest proposals
(`ConfirmedIncludedBetween`) give `ConfirmedExtendedByHonestProposalsBetween S Sched x tE t`.

Why: for an honest proposal `B` of slot `s` without a root collision, the proposer, an honest
active validator of slot `s`, has `B` as its confirmed tip right after the support cutoff of slot
`s + 1`, at a time from `tE` to `t` (the inclusion). A confirmed tip `C` of a validator honest
through a step at a time from `tE` to before the start of slot `s` is compatible with it (the
agreement). `C` is held then (`confirmedOf_mem_tree`), so `B`, of slot `s`
(`proposal_slot_parent`), is not `C` or an ancestor of `C` (`slot_lt_of_ancestorEq_held_before`):
`C` is an ancestor of `B` other than `B`.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read; `t`: the time up to which the
  updates are read. -/
theorem confirmedExtendedBetween_of_agree_included {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (tE t : ℕ)
    -- every time is reached; corruption is permanent
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    -- every slot starting at or after `tE` is at least `2`
    (h2 : ∀ s : ℕ, tE ≤ slotStart S s → 2 ≤ s)
    -- Lemma 90's agreement and inclusion from `tE` up to `t`
    (hAgree : ConfirmedAgreeBetween S Sched x tE t)
    (hIncl : ConfirmedIncludedBetween S Sched x tE t) :
    ConfirmedExtendedByHonestProposalsBetween S Sched x tE t := by
  rw [confirmedExtendedByHonestProposalsBetween_unfold]
  rw [GoldilocksCorrectness.Proofs.View.confirmedAgreeBetween_unfold] at hAgree
  rw [GoldilocksCorrectness.Proofs.View.confirmedIncludedBetween_unfold] at hIncl
  intro s hs hst hop B hB
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by have := h2 s hs; omega⟩
  have hBslot : B.slot = q + 2 := (proposal_slot_parent S Sched x (by omega) hB).1
  obtain ⟨ip, hl, hsent⟩ := hB
  rcases (hIncl (q + 2) hs hst hop).2 ip B hl hsent with hcol | ⟨hfirst, -⟩
  · exact Or.inl hcol
  right
  intro v i hv hi hlt
  have hp := opener_mem_honestActiveAt S Sched q hop
  have hconf := hfirst _ hp
  have hss : slotStart S (q + 2) ≤ supportCutoff S (q + 2 + 1) := by
    have := supportCutoff_eq S (q + 2 + 1)
    have := voteTime_eq S (q + 2 + 1)
    have := slotStart_mono S (show q + 2 ≤ q + 2 + 1 by omega)
    omega
  set j₁ := stepBefore x (supportCutoff S (q + 2 + 1) + 1) with hj₁def
  have htj₁ : x[j₁].time + 1 = supportCutoff S (q + 2 + 1) + 1 :=
    time_stepBefore_add_one x hDiv (by omega)
  have hpadv : S.P.proposer (q + 2) ∉ Sched.adv ((supportCutoff S (q + 2 + 1) : ℕ) : Int) :=
    (Finset.mem_sdiff.1 hp).2
  have hHon : HonestThrough x j₁ (S.P.proposer (q + 2)) := fun t' ht' had =>
    hpadv (hMono _ _ (le_trans ht' (by exact_mod_cast (show x[j₁].time ≤
      supportCutoff S (q + 2 + 1) by omega))) had)
  have hcomp := hAgree v (S.P.proposer (q + 2)) i j₁ hv hHon hi (by omega) (by omega) (by omega)
  have hst' : stateBefore x (supportCutoff S (q + 2 + 1) + 1) (S.P.proposer (q + 2)) =
      x[j₁][S.P.proposer (q + 2)].st := rfl
  rw [← hst', hconf] at hcomp
  have hCT : confirmedOf (x[i][v].st) ∈ (x[i][v].st).S.T :=
    confirmedOf_mem_tree _ (lem11_node_invariant S Sched x i v).1.2.2.2.1
  have hnot : ¬ B.AncestorEq (confirmedOf (x[i][v].st)) := fun h => by
    have := slot_lt_of_ancestorEq_held_before x hCT h hlt
    omega_nat
  rcases (compatible_iff _ _).1 hcomp with h | h
  · exact ⟨h, fun heq => hnot (heq ▸ ancestorEq_refl _)⟩
  · exact absurd h hnot

/-- **Lemma 90's fourth conclusion, with no upper end, from its agreement and its inclusion.** When
every slot starting at or after `tE` is at least `2`, `ConfirmedAgreeAfterHealing` and
`ConfirmedIncludedAfterHealing` give `ConfirmedExtendedByHonestProposals S Sched x tE`.

Why: at a slot `s`, both read up to the time `t := supportCutoff S (s + 1)`
(`confirmedAgreeAfterHealing_iff`, `confirmedIncludedAfterHealing_iff`), and
`confirmedExtendedBetween_of_agree_included` at that time.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read. -/
theorem confirmedExtended_of_agree_included {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (tE : ℕ)
    -- every time is reached; corruption is permanent
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    -- every slot starting at or after `tE` is at least `2`
    (h2 : ∀ s : ℕ, tE ≤ slotStart S s → 2 ≤ s)
    -- Lemma 90's agreement and inclusion from `tE` on
    (hAgree : ConfirmedAgreeAfterHealing S Sched x tE)
    (hIncl : ConfirmedIncludedAfterHealing S Sched x tE) :
    ConfirmedExtendedByHonestProposals S Sched x tE := by
  intro s hs hop b hb
  exact confirmedExtendedBetween_of_agree_included x tE (supportCutoff S (s + 1)) hDiv hMono h2
    ((confirmedAgreeAfterHealing_iff S Sched x tE).1 hAgree _)
    ((confirmedIncludedAfterHealing_iff S Sched x tE).1 hIncl _) s hs le_rfl hop b hb

/-! ## Lemma 98's second conclusion -/

/-- **Lemma 98's second conclusion from Lemma 86's compatibility and Lemma 98's first.** When the
finalized blocks of validators honest through steps at times at most `t` are pairwise compatible
(Lemma 86 read up to `t`), `FinalityIncludedBetweenEveryReader S Sched x tE t` gives
`FinalizedExtendedByHonestProposalsBetweenEveryReader S Sched x tE t`, the two with every
reader up to `t`.

Why: for a proposal `B` of slot `s` without a root collision, and a reader `v` after step `j`,
`FinalityIncludedBetweenEveryReader` makes `B` an ancestor of, or equal to, `v`'s finalized block,
and that finalized block one no validator had after a step at a time before the start of slot `s`. A
finalized block `F` of a validator honest through a step at a time from `tE` to before the start of
slot `s` is so not `v`'s, and is compatible with it (Lemma 86, both steps at times at most `t`).
If `v`'s were an ancestor of `F`, then `B` would be an ancestor of a block held before slot `s`
starts, while `B` has the slot `s` (`proposal_slot_parent`, `slot_lt_of_ancestorEq_held_before`).
So `F` is an ancestor of `v`'s other than it.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read; `t`: the time up to which the
  readers' steps are read. -/
theorem finalizedExtendedBetween_of_compatible_included {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (tE t : ℕ)
    -- Lemma 86 read up to `t`: the finalized blocks of honest validators are compatible
    (hCompat : ∀ (v₁ v₂ : V) (i j : ℕ), HonestThrough x i v₁ → HonestThrough x j v₂ →
      x[i].time ≤ t → x[j].time ≤ t →
      (x[i][v₁].st).S.F.compatible (x[j][v₂].st).S.F = true)
    -- Lemma 98's first conclusion from `tE` up to `t`
    (hIncl : FinalityIncludedBetweenEveryReader S Sched x (Δ S) tE t) :
    FinalizedExtendedByHonestProposalsBetweenEveryReader S Sched x (Δ S) tE t := by
  rw [finalizedExtendedByHonestProposalsBetweenEveryReader_unfold]
  rw [GoldilocksCorrectness.Proofs.View.finalityIncludedBetweenEveryReader_unfold] at hIncl
  intro s r hs hop hsr hwin hcut B hB
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      obtain ⟨ip, hl, -⟩ := hB
      have ht := (time_of_lbl_tickAllAwake x hl).1
      rw [slotStart_eq, Nat.mul_zero] at ht
      omega
    · exact h
  have hBslot : B.slot = s := (proposal_slot_parent S Sched x hs1 hB).1
  obtain ⟨ip, hl, hsent⟩ := hB
  rcases (hIncl s r hs hop hsr hwin hcut).2 ip B hl hsent with hc | hc | hmain
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  right; right
  intro v j hv hjt hAw w i hw _ hlt
  obtain ⟨hBF, hnew⟩ := hmain v j hv hjt hAw
  have hit : x[i].time ≤ t := by
    have h1 := slotStart_mono S (show s ≤ (r + 3) * S.C.R from le_trans hsr
      (Nat.mul_le_mul_right _ (by omega)))
    have := supportCutoff_eq S ((r + 3) * S.C.R)
    have := voteTime_eq S ((r + 3) * S.C.R)
    omega
  have hFT : (x[i][w].st).S.F ∈ (x[i][w].st).S.T := (lem11_node_invariant S Sched x i w).1.2.2.2.1
  refine ⟨?_, hnew w i hlt⟩
  rcases (compatible_iff _ _).1 (hCompat w v i j hw hv hit hjt) with h | h
  · exact h
  · exfalso
    have := slot_lt_of_ancestorEq_held_before x hFT (ancestorEq_trans hBF h) hlt
    omega_nat

end GoldilocksCorrectness.Proofs.Executions
