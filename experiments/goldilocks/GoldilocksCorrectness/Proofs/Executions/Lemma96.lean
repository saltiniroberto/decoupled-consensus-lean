module
public import GoldilocksCorrectness.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.ChainStateCertified

@[expose] public section

/-!
# Lemma 96: three consecutive honest round opening slots justify the middle proposal's height

The proof of Lemma 96, `lem96_consecutive_openings_justified`, stated in
`GoldilocksCorrectness/Statements/Executions/FinalityLivenessStatements.lean`, and the routine
fact it reads:

- `first_advance_justified_or_timeout`: the block that first takes a chain past a height either
  justified that height (its justification height is it) or passed the timeout test at its slot.

The route: the height step at the rounds `r − 1`, `r`
and at `r`, `r + 1` (`consecutive_openings_step_kit`) puts `T_h(B)` strictly after the previous
proposal, so at a slot after `(r − 1) R`; the block `Y` that takes `B'`'s chain past `h(B)` either
justified it, and the justification height only rises along a chain, or passed the timeout test,
`T_h(B).slot + δt ≤ Y.slot ≤ (r + 1) R`, which with `2R ≤ δt + 1` leaves only `Y = B'` with its
parent at `h(B)`; then `B'` justifies `T_h(B)` (Lemma 53), at the height `h(B)`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_mono voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_T_h_spec
  chainStateOf_node first_advance_justified_or_timeout lem47_chain_state_heights
  parent_ancestorEq_self)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_node_iff ancestorEq_of_parent? state_transition_cases state_transition_justification)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Lemma 96 -/

/-- **Lemma 96, three consecutive honest round opening slots justify the middle proposal's
height.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the middle round; `Bprev`, `B`, `B'`: the proposals of the rounds `r − 1`, `r`, `r + 1`. -/
theorem lem96_consecutive_openings_justified (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r : ℕ) (Bprev B B' : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S ((r + 1) * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ voteTime S ((r + 1) * S.C.R) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hδt : 2 * S.C.R ≤ S.C.δt + 1)
    (hr : 1 ≤ r) (hAfter : x[i₂].time < slotStart S ((r - 1) * S.C.R))
    (hOpenerPrev : HonestOpenerAt S Sched ((r - 1) * S.C.R))
    (hOpener : HonestOpenerAt S Sched (r * S.C.R))
    (hOpener' : HonestOpenerAt S Sched ((r + 1) * S.C.R))
    (hQuorumPrev : QuorumActiveAt S Sched ((r - 1) * S.C.R))
    (hQuorum : QuorumActiveAt S Sched (r * S.C.R))
    (hProposePrev : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r - 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r - 1) * S.C.R), NamedObject.block Bprev⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoColPrev : ¬ RootCollisionAtProposal S Sched x ((r - 1) * S.C.R) Bprev)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B') :
    (chainStateOf S.C B).h ≤ (chainStateOf S.C B').h_j := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀, r = r₀ + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hAfter hOpenerPrev hQuorumPrev hProposePrev hNoColPrev
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hmul : ∀ a : ℕ, (a + 1) * S.C.R = a * S.C.R + S.C.R := fun a => by
    rw [Nat.add_mul, Nat.one_mul]
  have hm1 := hmul r₀
  have hm2 := hmul (r₀ + 1)
  have hle01 : slotStart S (r₀ * S.C.R) ≤ slotStart S ((r₀ + 1) * S.C.R) :=
    slotStart_mono S (by omega)
  have hv12 : voteTime S ((r₀ + 1) * S.C.R) ≤ voteTime S ((r₀ + 1 + 1) * S.C.R) := by
    have := slotStart_mono S (show (r₀ + 1) * S.C.R ≤ (r₀ + 1 + 1) * S.C.R by omega)
    rw [voteTime_eq, voteTime_eq]
    omega
  -- the height step at the rounds `r₀`, `r₀ + 1`
  obtain ⟨hBpslot, hBslot, hPP, hPB, -, hBT, hstep1, -⟩ := consecutive_openings_step_kit S Sched x
    GST s₀ anchor i₂ H r₀ Bprev B hDiv hMono hSync hCatch hSyncF hCatchF (hRoots.mono hv12) hParent
    hOwner hU hAdvQ hSleepK hAnchor hGST ht₀
    (fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega))
    (fun s' h₁ h₂ => hInv s' h₁ (by omega)) (fun s' h₁ h₂ => hLocks s' h₁ (by omega)) hLocks₀ hOld
    (fun j w h₁ h₂ h₃ => hCaches j w h₁ (le_trans h₂ hv12) h₃) hParam hAfter hOpenerPrev hOpener
    hQuorumPrev hProposePrev hPropose hNoColPrev hNoCol
  -- the height step at the rounds `r₀ + 1`, `r₀ + 2`
  obtain ⟨-, hB'slot, hBP', hPB', hB'ne, hB'T, hstep2, hJ⟩ := consecutive_openings_step_kit S Sched
    x GST s₀ anchor i₂ H (r₀ + 1) B B' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner
    hU hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hParam
    (lt_of_lt_of_le hAfter hle01) hOpener hOpener' hQuorum hPropose hPropose' hNoCol hNoCol'
  -- the trees of the proposers of `(r₀ + 1) R` and `(r₀ + 2) R`
  have hTC := (lem11_node_invariant S Sched x (stepBefore x (voteTime S ((r₀ + 1) * S.C.R)))
    (S.P.proposer ((r₀ + 1) * S.C.R))).1.2.2.1
  have hTC' := (lem11_node_invariant S Sched x (stepBefore x (voteTime S ((r₀ + 1 + 1) * S.C.R)))
    (S.P.proposer ((r₀ + 1 + 1) * S.C.R))).1.2.2.1
  -- `T_h(B)` is a strict descendant of `Bprev`, so its slot is after `r₀ R`
  obtain ⟨hThB, hThh⟩ := chainStateOf_T_h_spec S.C B
  have hPB0 : Bprev.AncestorEq B := ancestorEq_trans hPP hPB
  have hThSlot : r₀ * S.C.R < (chainStateOf S.C B).T_h.slot := by
    rcases ancestorEq_compatible hThB hPB0 with h | h
    · exfalso
      have := (lem47_chain_state_heights S.C _ _).2.2.2.1 h
      rw [hThh] at this
      omega_nat
    · have hne : Bprev ≠ (chainStateOf S.C B).T_h := by
        intro heq
        rw [← heq] at hThh
        omega_nat
      have hThT : (chainStateOf S.C B).T_h ∈
          (x[stepBefore x (voteTime S ((r₀ + 1) * S.C.R))][S.P.proposer ((r₀ + 1) * S.C.R)].st).S.T :=
        ancestors_mem_T_of_exec S Sched x _ _ B _ hBT hThB
      have := slot_lt_of_ancestorEq_of_treeClosed hTC hThT h hne
      rw [hBpslot] at this
      exact this
  -- the block that takes `B'`'s chain past `h(B)`
  have hB1 := (lem47_chain_state_heights S.C B B).1.1
  obtain ⟨Y, hYB', hYne, hYp, hYh, hbranch⟩ := first_advance_justified_or_timeout S.C B'
    (chainStateOf S.C B).h hB1 (by omega_nat)
  have hYpY : Y.parent.AncestorEq Y := parent_ancestorEq_self Y
  have hBB' : B.AncestorEq B' := ancestorEq_trans hBP' hPB'
  have hTY : (chainStateOf S.C Y.parent).T_h = (chainStateOf S.C B).T_h := by
    rcases ancestorEq_compatible (ancestorEq_trans hYpY hYB') hBB' with h | h
    · exact (lem47_chain_state_heights S.C Y.parent B).2.2.2.2 h hYp
    · exact ((lem47_chain_state_heights S.C B Y.parent).2.2.2.2 h hYp.symm).symm
  rcases hbranch with hjY | hslotY
  · -- `Y` justified `h(B)`, and the justification height only rises along `B'`'s chain
    rw [← hjY]
    exact (GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono S.C Y B' hYB').1
  · -- the timeout test leaves only `Y = B'`, with its parent at `h(B)`
    rw [hTY] at hslotY
    have hYeq : Y = B' := by
      by_contra hne
      have := slot_lt_of_ancestorEq_of_treeClosed hTC' hB'T hYB' hne
      rw [hB'slot] at this
      have h2 : (r₀ + 1 + 1) * S.C.R = r₀ * S.C.R + 2 * S.C.R := by
        rw [hm2, hm1]
        omega
      omega_nat
    subst hYeq
    have hJB' := hJ hYp
    -- `B'`'s state transition justified its parent's `T_h`
    obtain ⟨P, s'', r'', votes, support, ats, v, hB'def⟩ : ∃ P s'' r'' votes support ats v,
        Y = Block.node P s'' r'' votes support ats v := by
      cases hY : Y with
      | genesis => exact absurd hY hYne
      | node P s'' r'' votes support ats v => exact ⟨P, s'', r'', votes, support, ats, v, rfl⟩
    subst hB'def
    change (chainStateOf S.C P).h = (chainStateOf S.C B).h at hYp
    change (chainStateOf S.C P).T_h = (chainStateOf S.C B).T_h at hTY
    rw [chainStateOf_node] at hJB' ⊢
    rcases state_transition_justification S.C (chainStateOf S.C P)
        (.node P s'' r'' votes support ats v) with ⟨hj, hJP⟩ | ⟨hj, -⟩
    · exfalso
      rw [hJP, ← hTY] at hJB'
      obtain ⟨-, hJ0, hJ1⟩ := chainStateOf_J_spec S.C P
      have hPb := (lem47_chain_state_heights S.C P P).1.2.1
      rcases Nat.eq_zero_or_pos (chainStateOf S.C P).h_j with h0 | hpos
      · have hg := hJ0 h0
        rw [hJB'] at hg
        rw [← hTY, hg] at hThSlot
        exact Nat.not_lt_zero _ hThSlot
      · have := hJ1 hpos
        rw [hJB', (chainStateOf_T_h_spec S.C P).2] at this
        omega_nat
    · rw [hj, hYp]
