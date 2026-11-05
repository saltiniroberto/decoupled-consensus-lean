module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityB6
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityB6
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityUpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDeliveryUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89StabilityB6UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89StabilityB6UpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a viable block of a validator
compared with another validator's state one delay before, and an eligible confirmation with an
honest supporter, with the delivery premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **`floor_le_of_delivery` read at the receiver's tick**. The holder `p`, outside the adversary set up to
the time `t`, active from `a` through the sync delay after it; the receiver `w` ticks to `c`, at least `t + Δ S`, at
the step `kR`, is active at every step from the real time `a` up to that tick, and ticked earlier to `c₂`, at least the
start of the slot of every block `p` holds before `t` and one delay before `c`. Then `p`'s `head_height_floor` before
`t` is at most `w`'s at its tick.

Why: as `floor_le_of_delivery`, with the blocks `p` holds before `t` (its contest block and its justification
witness) delivered by `w`'s tick (`block_at_tick_of_held_step`) in place of by a real time.

With the delivery premises up to `tE`, at least the clock value of the receiver's tick (`htE`), and the roots up
to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `t`: the time `p`'s state is read before; `a`: the start of the windows; `c`, `kR`: the clock value
  and the step of `w`'s tick; `c₂`, `k₂`: those of its earlier tick; `p`, `w`: the holder and the receiver.

Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: the `head_height_floor` of an honest validator before a time is at most that of another, read at its
tick one delay later. -/
theorem floor_le_of_delivery_tick_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t a c c₂ kR k₂ : ℕ) (p w : V)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a third of the validators have been in the adversary set up to the real time of `kR`
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kR))
    -- from `a` on, one delay or one sync delay before `t + Δ`, the network is synchronous
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S)
    -- the holder `p`, active from `a` through the sync delay after it, outside the adversary set up to `t`
    (hv₀ : p ∈ A.activeThroughout x a (a + Δs)) (hp : p ∉ A.corruptedAtTime x t)
    -- the receiver `w`'s tick to `c`, at least one delay after `t`, and its window from `a`
    (hkR : x.lbl kR = Event.tick w c) (hcu : t + Δ S ≤ c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- an earlier tick of `w` to `c₂`, one delay before `c`, at least the start of every slot of `p`'s blocks
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t p).tree, M.slotStart S.C Y.slot ≤ c₂)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    M.head_height_floor (x.stateBefore t p) ≤ M.head_height_floor (x.st kR w) := by
  -- `dev`'s proof of `floor_le_of_delivery_unordered`, with `w` read at its tick `kR` (rule R3) and `p`'s blocks
  -- delivered by that tick (`block_at_tick_of_held_step`) in place of by the real time `t + Δ S` (F-P1-25-1)
  classical
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨kp, hkp⟩ : ∃ kp : ℕ, kp = x.stepBefore t := ⟨_, rfl⟩
  have hsb : x.stateBefore t p = x.st kp p := by rw [hkp]; rfl
  rw [hsb] at hslot ⊢
  have hkpt : x.time kp ≤ (t : ℝ) := by rw [hkp]; exact (time_stepBefore_le M) x R E t
  have hpk : p ∉ A.corrupted kp := (not_mem_corrupted_of_le_time M) x R E hp hkpt
  have hwk : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hcuR : (t : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hcu
  have hkpR : x.time kp ≤ x.time kR := by linarith
  have hkpR' : x.time kp ≤ tR := hkpR.trans htR
  have hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (max (x.time kR) (x.time kp)) :=
    hAdv.mono (max_le le_rfl hkpR)
  have htRt : ((t : ℕ) : ℝ) ≤ tR := by linarith
  have hRootsT : RootsNameBlocksUntil M A x (t : ℕ) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htRt hRoots
  -- the invariants of the two states
  have hInvP := (lem11_node_invariant M F S A x R E kp p hpk).1
  have hInvW := (lem11_node_invariant M F S A x R E kR w hwk).1
  have hCacheW : GoldilocksCorrectness.Record.Statements.Routines.HeightCacheBounds M S.C (x.st kR w) :=
    fun _ hB => GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hB
  -- every block `p` holds at `kp` (compatible with its finalized block there) that is compatible with `w`'s
  -- finalized block at `kR` reaches `w` by its tick `kR`
  have hreach : ∀ Y ∈ (x.st kp p).tree,
      (x.st kp p).finalized.compatible Y = true →
      (x.st kR w).finalized.compatible Y = true →
      Y ∈ (x.st kR w).tree := by
    intro Y hY hsel hc
    by_cases hg : Y = Block.genesis
    · subst hg
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    have hak : x.stepBefore a ≤ kp := by
      rw [hkp]; exact (stepBefore_mono M) x R E (show a ≤ t by omega)
    have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E p hak) hsel
    exact block_at_tick_of_held_step M F U S A x R GST tE t kp a c c₂ kR k₂ p w Y
      E hNet hSkew hRedeliver Sy
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htR hRoots) hParent hGSTa
      (by omega) hcu htE hv₀ hkpt hpk hY hFa hg hkR hwin hk₂ hc₂ (hslot Y hY) hc
  -- `w`'s finalized block is the finalized block of some held block's chain
  obtain ⟨Bw, hBw, hFw⟩ := (finalizedFromChain_of_exec M F) S A x R E kR w
  have hBwh : (M.chainStateOf S.C Bw).h ≤ hMax M S.C (x.st kR w) := hCacheW Bw hBw
  have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Bw Bw).1
  -- a block `p` holds at a chain-state height at least `w`'s greatest chain-state height is on
  -- `w`'s finalized block's chain (Lemma 89a)
  have hpast : ∀ Y ∈ (x.st kp p).tree,
      hMax M S.C (x.st kR w) ≤ (M.chainStateOf S.C Y).h →
      (x.st kR w).finalized.AncestorEq Y := by
    intro Y hY hYh
    have hlt : (M.chainStateOf S.C Bw).h_F < (M.chainStateOf S.C Y).h :=
      lt_of_le_of_lt h47.2.2 (lt_of_lt_of_le h47.2.1 (le_trans hBwh hYh))
    have hFY := (lem68_honest_past_finalized M F Fx) S A x R E hRoots kR kp w p Bw Y hThird hwk hpk
      hBw hY hlt (max_le htR hkpR')
    rw [hFw]
    exact hFY
  -- step A: `p`'s greatest chain-state height is at most `w`'s
  obtain ⟨⟨Dp, hDpT, hDpJ, hDpj⟩, ⟨X, hXT, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kp p
  obtain ⟨⟨Dw, hDwT, hDwJ, hDwj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kR w
  have hm : hMax M S.C (x.st kp p) ≤ hMax M S.C (x.st kR w) := by
    by_contra hcon
    have hcon' : hMax M S.C (x.st kR w) < (M.chainStateOf S.C X).h := by
      rw [hXh]
      exact Nat.lt_of_not_le hcon
    have hFX := hpast X hXT (le_of_lt hcon')
    -- `X`, of the greatest chain-state height in `p`'s tree, descends from `p`'s finalized block
    have hFpX : (x.st kp p).finalized.AncestorEq X :=
      (hMax_witness_compatible_finalized M F Fx) x R E hRootsT kp p X (hAdv.mono hkpR) hpk hXT
        (fun B hB => by
          rw [hXh]
          exact GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hB) hkpt
    have hXw := hreach X hXT ((compatible_iff _ _).2 (Or.inl hFpX)) ((compatible_iff _ _).2 (Or.inl hFX))
    have h2 : (M.chainStateOf S.C X).h ≤ hMax M S.C (x.st kR w) := hCacheW X hXw
    exact absurd h2 (Nat.not_le.2 hcon')
  have hfw := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.st kR w) hInvW
  have key1 : ∀ a b c : ℕ, a ≤ b → b ≤ c + 1 → a - 1 ≤ c := by intros; omega
  have key2 : ∀ a b c : ℕ, a < b → b ≤ c + 1 → a ≤ c := by intros; omega
  have key3 : ∀ a m hj bj bh hm : ℕ, a = m - 1 → a ≤ hj → hj = bj → bj < bh → bh ≤ hm →
      hm = m → hj = m - 1 := by intros; omega
  have key4 : ∀ m hj hm : ℕ, hm = m → hj = m - 1 → 1 ≤ m - 1 → hm = hj + 1 := by intros; omega
  -- step B: by `p`'s box
  cases hcp : M.fg_contest (x.st kp p) with
  | false =>
      have hfloor : M.head_height_floor (x.st kp p) = hMax M S.C (x.st kp p) - 1 := by
        exact (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
          (x.st kp p) hInvP hcp
      rw [hfloor]
      exact key1 _ _ _ hm hfw
  | true =>
      obtain ⟨hbox, -, hfloor⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X
          (x.st kp p) hInvP hcp
      rw [hfloor]
      -- the block that makes `p` contested
      obtain ⟨-, B', hB'T, hFB', hB'h, hJB'⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X
        (x.st kp p) hInvP hcp
      rcases Nat.lt_or_ge (hMax M S.C (x.st kp p)) (hMax M S.C (x.st kR w)) with hlt | hge
      · exact key2 _ _ _ hlt hfw
      have heq : hMax M S.C (x.st kR w) = hMax M S.C (x.st kp p) := le_antisymm hge hm
      have hFwB' : (x.st kR w).finalized.AncestorEq B' :=
        hpast B' hB'T (by
          show hMax M S.C (x.st kR w) ≤ (M.chainStateOf S.C B').h
          rw [heq, hB'h])
      have hB'w := hreach B' hB'T ((compatible_iff _ _).2 (Or.inl hFB')) ((compatible_iff _ _).2 (Or.inl hFwB'))
      -- `p`'s justified block is justified at its greatest chain-state height minus one, at least `1`
      have hjp : (M.chainStateOf S.C Dp).h_j = hMax M S.C (x.st kp p) - 1 := by
        rw [← hDpj, hbox, Nat.add_sub_cancel]
      have hj1 : 1 ≤ (M.chainStateOf S.C Dp).h_j := by
        rcases Nat.eq_zero_or_pos (M.chainStateOf S.C Dp).h_j with h0 | hpos
        · exfalso
          have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Dp).2.1 h0
          rw [← hDpJ] at hg
          rw [hg] at hJB'
          exact hJB' (genesis_ancestorEq _)
        · exact hpos
      -- `Dp` reaches `w`, so `w`'s justification height is at least that height minus one
      have hDp47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dp Dp).1.2.1
      have hFwDp : (x.st kR w).finalized.AncestorEq Dp :=
        hpast Dp hDpT (by rw [heq]; unfold Height at *; omega)
      have hFpJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E kp p
      have hJDp := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Dp).1
      rw [← hDpJ] at hJDp
      have hDpw := hreach Dp hDpT ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFpJ hJDp)))
        ((compatible_iff _ _).2 (Or.inl hFwDp))
      have hjw1 := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR w Dp
        hDpw hFwDp
      -- and at most that height minus one
      have hDwh := hCacheW Dw hDwT
      have h47w := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dw Dw).1.2.1
      have hjw : (x.st kR w).justifiedHeight = hMax M S.C (x.st kp p) - 1 :=
        key3 _ _ _ _ _ _ hjp hjw1 hDwj h47w hDwh heq
      -- the two justified blocks are one block
      have hcertP := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dp).1 hj1).1
      have hjj : (M.chainStateOf S.C Dw).h_j = (M.chainStateOf S.C Dp).h_j :=
        hDwj.symm.trans (hjw.trans hjp.symm)
      have hj1w : 1 ≤ (M.chainStateOf S.C Dw).h_j := hjj ▸ hj1
      have hcertW := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dw).1 hj1w).1
      rw [hjj] at hcertW
      have hroots := (lem76_honest_one_justification M F Fx) S A x R E kR kp w p hThird Dw Dp hDwT hDpT
        _ _ _ hcertW hcertP
      have hJwT := ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E kR w).2.2.1
      have hJpT := ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E kp p).2.2.1
      have hJJ : (x.st kR w).justified = (x.st kp p).justified := by
        rw [hDwJ, hDpJ]
        refine hRoots _ _
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hwk htR ?_)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hpk hkpR' ?_) hroots
        · rw [← hDwJ]
          exact hJwT
        · rw [← hDpJ]
          exact hJpT
      -- `w` is contested by `B'`
      have hcw : M.fg_contest (x.st kR w) = true := by
        refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X
          (x.st kR w) hInvW B' (key4 _ _ _ heq hjw (hjp ▸ hj1)) hB'w hFwB' ?_ ?_
        · show (M.chainStateOf S.C B').h = _
          rw [heq]
          exact hB'h
        · rw [hJJ]
          exact hJB'
      obtain ⟨-, -, hfloorw⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X
          (x.st kR w) hInvW hcw
      rw [hfloorw, heq]


/-- **A viable head of the receiver at its tick bounds the holder's `head_height_floor`**. Under the hypotheses of
`floor_le_of_delivery_tick_upTo`: when `W` is a viable head of `w`'s frame at its tick `kR`, `p`'s `head_height_floor`
before `t` is at most `W`'s chain-state height.

Why: `floor_le_of_delivery_tick_upTo`, and a viable head is at a chain-state height at least `head_height_floor`
(`mem_viable_heads_iff_of_core`, with the node invariant at `kR`).

With the delivery premises up to `tE`, at least the clock value of the receiver's tick (`htE`), and the roots up
to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others: as `floor_le_of_delivery_tick_upTo`; `W`: the block.

Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: the `head_height_floor` of an honest validator before a time is at most the chain-state height of any
viable head of another, read at its tick one delay later. -/
theorem floor_le_of_viable_tick_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t a c c₂ kR k₂ : ℕ) (p w : V) (W : Block V)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kR))
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S)
    (hv₀ : p ∈ A.activeThroughout x a (a + Δs)) (hp : p ∉ A.corruptedAtTime x t)
    (hkR : x.lbl kR = Event.tick w c) (hcu : t + Δ S ≤ c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t p).tree, M.slotStart S.C Y.slot ≤ c₂)
    (hW : W ∈ (M.fg_to_ac (x.st kR w)).viable_heads)
    (htR : x.time kR ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    M.head_height_floor (x.stateBefore t p) ≤ (M.chainStateOf S.C W).h := by
  have h := (floor_le_of_delivery_tick_upTo M F U Fx) S A x R GST t a c c₂ kR k₂ p w E hNet hSkew hRedeliver Sy hRoots
    hParent hAdv hGSTa ha hv₀ hp hkR hcu hwin hk₂ hc₂ hslot htR htE
  obtain ⟨-, -, -, hfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
    (show M.nodeInvCore S.C S.P S.X (x.st kR w) from (lem11_node_invariantCore_of_run M F S x R kR w).1) W).1 hW
  exact le_trans h hfl

/-! ## An honest vote and the viable blocks of its voter -/


/-- **A saved confirmation has an honest supporter.** When the confirmation read on `v`'s node
state right after the support cutoff of slot `σ + 1` is `X`, with `v` awake and honest from the
duty window's start of slot `σ + 1` to that cutoff (`update_state_of_duty`), some member `u` of
`Hs` put on the wire at the vote time of slot `σ` its vote for a block it held, `X` or a
descendant of `X`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `σ`: the slot of the votes; `v`: the updater; `Hs`: the honest voters;
  `X`: the confirmation.

Roots name blocks until the real time of `v`'s tick to the support cutoff of slot `σ + 1`, where its update runs
(rule R3; F-P1-18).

Restated with the delivery premises up to `M.supportCutoff S.C σ`.

Read aloud: a saved confirmation of an honest validator has an honest supporter, with the delivery
premises up to the bound. -/
theorem honest_supporter_of_saved_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST σ : ℕ) (v : V) (Hs : Finset V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C σ)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C σ))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (σ + 1)))))
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ)
    (hHs : ∀ u ∈ Hs, u ∈ honestActiveAt M S A x σ ∧ u ∈ S.P.committee σ)
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ) <
      2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (M.supportCutoff S.C (σ + 1)))
    (X : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X) :
    ∃ u ∈ Hs, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) ∧
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  classical
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hv₁ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hv₃ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hvfz := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S σ
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hm : max (Δ S) Δs ≤ M.supportCutoff S.C σ := by omega
  have hmR : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hcmR : ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) =
      ((M.supportCutoff S.C σ : ℕ) : ℝ) - max (Δ S : ℝ) (Δs : ℝ) := by
    rw [Nat.cast_sub hm, hmR]
  have hc0R : ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 2 * (Δ S : ℝ) := by
    have : M.supportCutoff S.C σ = 4 * Δ S * σ + 2 * Δ S := by omega
    rw [this]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 6 * (Δ S : ℝ) := by
    have : M.supportCutoff S.C (σ + 1) = 4 * Δ S * σ + 6 * Δ S := by rw [hc1, hv₃, hss1]; ring
    rw [this]; push_cast; ring
  have hvtR : ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + (Δ S : ℝ) := by
    rw [hv₁, hss0]; push_cast; ring
  have hss : M.slotStart S.C (σ + 1) = M.slotStart S.C σ + 4 * Δ S := by
    rw [hss1, hss0, Nat.mul_add, Nat.mul_one]
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hdw0 := duty_window_start_real S σ
  have hdw1 : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (σ : ℝ) + 5 * (Δ S : ℝ) - 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
    rw [duty_window_start_real S (σ + 1)]; push_cast; ring
  have hDk : (0 : ℝ) ≤ (Δ S : ℝ) * (S.C.k : ℝ) := by positivity
  have hΔs' : max (Δ S : ℝ) (Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := hΔs
  -- the tick to the cutoff and the update it runs, from `v`'s tick input
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨n'', sent, hrun, hAw, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R σ v E hk
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (σ + 1)))
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R σ v n'' sent hrun hAw
  rw [hsave] at hX
  have htk : x.tickStep v (M.supportCutoff S.C (σ + 1)) = k := (tickStep_eq_of_lbl M) x E hk
  have hti : x.tickInput v (M.supportCutoff S.C (σ + 1)) = x.st k v := by
    unfold Trace.tickInput; rw [htk]
  have hvk : v ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  have hkt := (E.tick_active k v _ hk).2.1
  rw [hc1R] at hkt
  -- `v` is active from `max (Δ S) Δs` before the support cutoff of slot `σ` to that cutoff
  have hvW : v ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) :=
    (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hv
      (by rw [hcmR, hc0R, hdw1]; have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith)
      (by
        have : M.voteTime S.C σ + Δ S + 4 * Δ S = M.supportCutoff S.C (σ + 1) := by omega
        have h' : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) + 4 * Δ S = ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
          exact_mod_cast this
        linarith)
  -- `v` is active from `ΔClockAhead` before the vote time of slot `σ` up to its tick `k`
  obtain ⟨kT, hkT, hwinT⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := ((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead)
    (by rw [hvtR, hdw1]; have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith)
  have hkTk : kT = k := by
    rw [← (tickStep_eq_of_lbl M) x E hkT, (tickStep_eq_of_lbl M) x E hk]
  rw [hkTk] at hwinT
  have hcR : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 2 * (Δ S : ℝ) := by
    rw [Nat.cast_add, hvtR]; ring
  -- `v`'s tick `kR` to the support cutoff of slot `σ` (`voteTime σ + Δ S`), before `kT`
  obtain ⟨kR, hkR, hkR1, hkR2⟩ := E.tick_of_active (M.voteTime S.C σ + Δ S) (by omega) v fun i h1 h2 => by
    refine hwinT i (by rw [hvtR]; rw [hcR] at h1; linarith) ?_
    exact ((lt_of_time_lt M) x R (by rw [hcR] at h2; linarith)).le
  have hkRk : kR ≤ k := ((lt_of_time_lt M) x R (by rw [hcR] at hkR2; linarith)).le
  -- the supporters' votes
  have hvotes : ∀ u ∈ Hs, ∃ (i : ℕ) (vote : GoldfishVote V),
      x.lbl i = Event.tick u (M.voteTime S.C σ) ∧ vote.val_index = u ∧ vote.slot = σ ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i :=
    fun u hu => (honest_active_votes M F U) S A x R σ u E hSkew (hHs u hu).1 (hHs u hu).2
  choose iv₀ vf₀ hvf₀ using hvotes
  let iv : V → ℕ := fun u => if h : u ∈ Hs then iv₀ u h else 0
  let vf : V → GoldfishVote V := fun u => if h : u ∈ Hs then vf₀ u h else GoldfishVote.mk u σ
    (Block.genesis : Block V).root
  have hvf : ∀ u ∈ Hs, x.lbl (iv u) = Event.tick u (M.voteTime S.C σ) ∧
      (vf u).val_index = u ∧ (vf u).slot = σ ∧
      (⟨u, NamedObject.gfVote (vf u)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (iv u + 1) - x.sent (iv u) := by
    intro u hu
    simp only [iv, vf, dif_pos hu]
    exact hvf₀ u hu
  have hslot : M.slot S.C (M.voteTime S.C σ) = σ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hcut : ((((M.voteTime S.C σ + Δ S : ℕ) : Int)) : Stamp) =
      ((S.C.t_ σ + 2 * S.C.Δ : Time) : Stamp) := by
    rw [show M.voteTime S.C σ + Δ S = M.supportCutoff S.C σ by omega,
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
  have hlt : S.C.t_ σ + 2 * S.C.Δ < S.C.t_ σ + 6 * S.C.Δ :=
    Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) S.C.Δ_pos) _
  -- each supporter's vote is in `v`'s pool at its tick input, stamped in time, and the only one of its voter there
  have hpool : ∀ u ∈ Hs, vf u ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ ∧
      (vf u).val_index = u ∧
      (∃ τ : Stamp, (x.tickInput v (M.supportCutoff S.C (σ + 1))).voteStamp (vf u) =
        some τ ∧ τ < ((S.C.t_ σ + 6 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ,
        vote'.val_index = u → vote' = vf u := by
    intro u hu
    obtain ⟨hl, hval, hsl, hsent⟩ := hvf u hu
    have huc1 : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := fun h =>
      (Finset.mem_sdiff.1 (hHs u hu).1).2 (Finset.mem_union_left _ h)
    have huk : u ∉ A.corrupted k := fun h =>
      (Finset.mem_sdiff.1 (hHs u hu).1).2 (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, k, v, hk, hvk, h⟩))
    have hsent' : (⟨(vf u).val_index, NamedObject.gfVote (vf u)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (iv u + 1) - x.sent (iv u) := by rw [hval]; exact hsent
    have hcomm : (vf u).val_index ∈ S.P.committee (vf u).slot := by
      rw [hval, hsl]; exact (hHs u hu).2
    have hu₀ : (vf u).val_index ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
        ((M.voteTime S.C σ : ℕ) : ℝ) := by
      rw [hval]
      exact (mem_activeThroughout_of_honestActiveAt M F) R E (hHs u hu).1
        (by rw [hcmR, hc0R, hdw0]; have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith)
        (by rw [hvtR, hc1R]; linarith)
    -- the vote is in `v`'s pool at its tick `kR` to the support cutoff of slot `σ`, from the send
    have hukR : u ∉ A.corrupted kR := Activity.not_mem_corruptedAtTime.1 huc1 kR (by
      rw [hc1R]; rw [hcR] at hkR2; linarith)
    have hlt1 := (E.tick_active _ u _ hl).2
    have heT : x.time (iv u + 1) ≤ ((M.voteTime S.C σ : ℕ) : ℝ) + ΔClockBehind := by
      rw [R.time_keep (iv u) (by rw [hl]; exact nofun)]; exact hlt1.2
    have hpoolR : vf u ∈ M.votesHeldSet (x.st kR v) σ := by
      rcases (pool_vote_at_tick_of_send M F U) S A x R GST σ (M.voteTime S.C σ) (M.supportCutoff S.C σ) u v
          (vf u) E hNet hSkew hRedeliver (by omega) (by omega) (by
            have hss2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (σ + 2)
            rw [hss2, Nat.mul_add]; omega) hsl
          (by rw [hval]; exact (hHs u hu).2) (by omega) (by omega) (iv u) hsent
          (E.not_mem_corrupted_of_tick hl) heT (((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead)
          (by have := R.time_le_succ (iv u); linarith [hlt1.1])
          le_rfl
          kR hkR (fun j hj1 hj2 => hwinT j hj1 (hj2.trans hkRk)) with
        h | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
      · exact h
      · exact absurd ((unique_vote_of_owner_at M F R) E hOwner hukR h₁ h₂ (hi₁.trans hval)
          (hi₂.trans hval)) hne
    have hpool₂ : vf u ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ := by
      rw [hti]; exact (pool_mono M F) x R E v hkRk σ hpoolR
    refine ⟨hpool₂, hval, ?_, fun vote' hv' hi' => ?_⟩
    · -- stamped before the support cutoff of slot `σ + 1` at `v`'s tick to it
      have hpk : vf u ∈ M.votesHeldSet (x.st k v) σ := by rw [← hti]; exact hpool₂
      obtain ⟨τ, hτ, hτlt⟩ := (voteStamp_lt_of_tick_of_active M F) R E hk
        (by rw [hc1]; omega)
        (fun j hj1 hj2 => hwinT j (by rw [hvtR]; rw [hc1R] at hj1; linarith) hj2) hpk
      refine ⟨τ, by rw [hti]; exact hτ, ?_⟩
      have hc6 : (((M.supportCutoff S.C (σ + 1) : ℕ) : Int) : Stamp) =
          ((S.C.t_ σ + 6 * S.C.Δ : Time) : Stamp) := by
        rw [show M.supportCutoff S.C (σ + 1) = (M.voteTime S.C σ + Δ S) + 4 * Δ S by omega]
        have h2 := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
        have h3 : ((((M.voteTime S.C σ + Δ S : ℕ) : Int)) : Stamp) = ((S.C.t_ σ + 2 * S.C.Δ : Time) : Stamp) := hcut
        have h4 : (((M.voteTime S.C σ + Δ S : ℕ) : Int)) = S.C.t_ σ + 2 * S.C.Δ := by exact_mod_cast h3
        have h5 : (((M.voteTime S.C σ + Δ S + 4 * Δ S : ℕ) : Int)) = S.C.t_ σ + 6 * S.C.Δ := by
          rw [Nat.cast_add, h4, Nat.cast_mul, h2]; push_cast; ring
        rw [h5]
      rw [hc6] at hτlt
      exact hτlt
    · rw [hti] at hv' hpool₂
      exact (unique_vote_of_owner_at M F R) E hOwner huk hv' hpool₂ hi' hval
  -- the update's walk ends at a block with the head root of some supporter's vote
  have hRI : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (σ + 1)))).tree := by
    rw [hti]; exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E k v
  obtain ⟨u, hu, H, hH, hr, hXH⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_supporter F) Hs vf
    hRI hpool hVoters hUpdate X hX
  obtain ⟨hl, hval, hsl, hsent⟩ := hvf u hu
  obtain ⟨H_u, hHT, hvote, -⟩ := (honest_vote_spec M F U) S A x R E σ u (vf u) ⟨iv u, hl, hsent⟩
  refine ⟨u, hu, vf u, ⟨iv u, hl, hsent⟩, H_u, hHT, hvote, ?_⟩
  -- the block of `v`'s tree with the vote's head root is `H_u`: both are held by honest validators by `v`'s tick
  have hHv : H ∈ (x.st k v).tree := by
    have := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).1
    rw [hti] at this; exact this
  have htu : x.tickStep u (M.voteTime S.C σ) = iv u := (tickStep_eq_of_lbl M) x E hl
  have hHTu : H_u ∈ (x.st (iv u) u).tree := by
    have := hHT; unfold Trace.tickInput at this; rw [htu] at this; exact this
  have hui : u ∉ A.corrupted (iv u) := E.not_mem_corrupted_of_tick hl
  have hit := (E.tick_active (iv u) u _ hl).2.2
  rw [hvtR] at hit
  have hroot : H.root = H_u.root := by rw [hr, hvote]
  have hHH : H = H_u :=
    hRoots H H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := v) hvk (by rw [htk]) hHv) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := iv u) (v := u) hui (by rw [htk]; linarith) hHTu) hroot
  rw [← hHH]
  exact hXH

end GoldilocksCorrectness.Record.Proofs.Executions

