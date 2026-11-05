module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Proofs.Executions.HealedFrame
public import GoldilocksCorrectness.Proofs.Executions.Lemma53
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Proofs.Routines.Certificates

@[expose] public section

/-!
# Lemma 89, part B: no honest `h_j` reaches a waiting opening's height before the next one

The proofs of the waiting openings' entry, landed byte for byte from
`scratch/goldilocks_healed/probe_wait_1.lean`:

- `honest_proposal_above_h_j`: an honest proposal made at the start of slot `s + 1` has a
  chain-state height at least one more than its proposer's `h_j` then;
- `change_of_h_j_reaches`: a validator whose `h_j` reaches `h` at `t`, with `head_height_floor` at
  most `h` after `t` and its justified block after `t` not the genesis block, has a
  `ForkChoiceChangeAt` at `t`;
- `h_j_lt_of_later_proposal`, `J_genesis_of_h_j_le_one`, `h_j_lt_or_genesis_before_cutoff`: before
  the later opening's support cutoff, no honest validator has `h_j` at least the waited height `h`
  (other than with the genesis block as justified block).

The waiting steps that use them, `quiet_waiting_next_proposal` and
`quiet_waiting_same_entry_cutoff` (two waiting quiet openings at one height share the height's
entry), are proved in `Proofs/Executions/Lemma89ClimbLate.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (h_max_le_floor_add_one h_max_sub_one_le_floor
  mem_viable_heads_iff root_cases)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_h fc_root_eq floor_cases)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_T_h)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm ancestorEq_genesis_iff)

open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **An honest proposal is higher than its proposer's justification.** -/
theorem honest_proposal_above_h_j (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    (stateBefore x (slotStart S (s + 1)) p).S.h_j + 1 ≤ (chainStateOf S.C B).h := by
  have hPV := proposal_parent_viable_head S Sched x s B p hPropose
  obtain ⟨iB, hl, hsent⟩ := hPropose
  obtain ⟨-, hBg, hpar?, -⟩ := proposal_parent_walk_end S Sched x s iB B p hl hsent
  have hPB := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hpar?
  obtain ⟨hPT, -, hRP, hflP⟩ := (mem_viable_heads_iff _ _).1 hPV
  rw [σ_eq_of_stateBefore S Sched x _ p _ hPT] at hflP
  have hmono := (lem47_chain_state_heights S.C B.parent B).2.2.2.1 hPB
  have hjl := h_j_lt_h_max S Sched x (slotStart S (s + 1)) p
  have hml := h_max_sub_one_le_floor (stateBefore x (slotStart S (s + 1)) p).S
  by_cases hhi : (stateBefore x (slotStart S (s + 1)) p).S.h_j + 1 ≤
      (chainStateOf S.C B.parent).h
  · unfold Height at *
    omega
  have hm1 : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
      (stateBefore x (slotStart S (s + 1)) p).S.h_j + 1 := by
    unfold Height at *
    omega
  have hc : fg_contest (stateBefore x (slotStart S (s + 1)) p).S = false := by
    cases hc' : fg_contest (stateBefore x (slotStart S (s + 1)) p).S
    · rfl
    · exfalso
      have hfl : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S =
          (stateBefore x (slotStart S (s + 1)) p).S.h_max := by
        rcases floor_cases (stateBefore x (slotStart S (s + 1)) p).S with ⟨-, -, h⟩ | ⟨h, -⟩
        · exact h
        · rw [hc'] at h; cases h
      unfold Height at *
      omega
  have hroot : get_fc_root (stateBefore x (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S.J := by
    rcases root_cases (stateBefore x (slotStart S (s + 1)) p).S with ⟨h, -, -⟩ | ⟨-, h | h⟩
    · exact h
    · rw [hc] at h; cases h
    · exact absurd hm1 h
  have hfc : (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root =
      get_fc_root (stateBefore x (slotStart S (s + 1)) p).S :=
    fc_root_eq _
  rw [hfc, hroot] at hRP
  have hPh : (chainStateOf S.C B.parent).h = (stateBefore x (slotStart S (s + 1)) p).S.h_j := by
    unfold Height at *
    omega
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (slotStart S (s + 1)) p
  by_cases hj0 : (stateBefore x (slotStart S (s + 1)) p).S.h_j = 0
  · have := (lem47_chain_state_heights S.C B B).1.1
    unfold Height at *
    omega
  have hj1 : 1 ≤ (chainStateOf S.C D).h_j := by
    unfold Height at *
    omega
  obtain ⟨hcert, -, -⟩ := (GoldilocksCorrectness.Proofs.Routines.lem66_chain_state_certified S.C D).1 hj1
  have hJh := (chainStateOf_J_spec S.C D).2.2 hj1
  have hEntry : (chainStateOf S.C (chainStateOf S.C D).J).T_h = (chainStateOf S.C D).J := by
    rcases chainStateOf_J_entry S.C D with h | h
    · rw [h, chainStateOf_genesis_T_h]
    · exact h
  rw [hJD] at hRP
  have hTh : (chainStateOf S.C B.parent).T_h = (chainStateOf S.C D).J := by
    have he := (lem47_chain_state_heights S.C (chainStateOf S.C D).J B.parent).2.2.2.2 hRP
      (by rw [hJh, hPh, hjD])
    rw [← he, hEntry]
  obtain ⟨A, hA, hAv⟩ := hcert
  have hPool : ∀ u ∈ A, ∃ a ∈ (stateBefore x (slotStart S (s + 1)) p).S.attestations,
      a.val_index = u ∧ a.h = (chainStateOf S.C B.parent).h ∧
        a.T = (chainStateOf S.C B.parent).T_h.root ∧ a.τ = false := by
    intro u hu
    obtain ⟨a, hav, hah, haT, haτ, hach⟩ := hAv u hu
    have hmem := pool_holds_chain_attestations S Sched x (stepBefore x (slotStart S (s + 1))) p D a
      hD hach
    refine ⟨a, hmem, hav, ?_, ?_, haτ⟩
    · rw [hah, hPh, hjD]
    · rw [haT, hTh]
  have h53 := lem53_next_honest_proposal_carries_certificate S Sched x (s + 1) p B B.parent A
    ⟨iB, hl, hsent⟩ rfl hA
    (fun u hu => by
      obtain ⟨a, ha, h1, h2, h3, -⟩ := hPool u hu
      exact ⟨a, ha, h1, h2, h3⟩)
  have := (h53.2 hPool).1
  unfold Height at *
  omega

/-- **Reaching a justification height `h` with `head_height_floor` at most `h` is a
fork-choice change.** -/
theorem change_of_h_j_reaches (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (w : V) (t h : ℕ)
    (hlo : (stateBefore x t w).S.h_j < h) (hhi : h ≤ (stateBefore x (t + 1) w).S.h_j)
    (hfl : head_height_floor (stateBefore x (t + 1) w).S ≤ h)
    (hJg : (stateBefore x (t + 1) w).S.J ≠ Block.genesis) :
    ForkChoiceChangeAt S Sched x w t := by
  have hjl' := h_j_lt_h_max S Sched x (t + 1) w
  have hmx' := h_max_le_floor_add_one (stateBefore x (t + 1) w).S
  have hm1 : (stateBefore x (t + 1) w).S.h_max = (stateBefore x (t + 1) w).S.h_j + 1 := by
    unfold Height at *
    omega
  have hc : fg_contest (stateBefore x (t + 1) w).S = false := by
    cases hc' : fg_contest (stateBefore x (t + 1) w).S
    · rfl
    · exfalso
      have hf : head_height_floor (stateBefore x (t + 1) w).S =
          (stateBefore x (t + 1) w).S.h_max := by
        rcases floor_cases (stateBefore x (t + 1) w).S with ⟨-, -, h⟩ | ⟨h, -⟩
        · exact h
        · rw [hc'] at h; cases h
      unfold Height at *
      omega
  have hroot : get_fc_root (stateBefore x (t + 1) w).S = (stateBefore x (t + 1) w).S.J := by
    rcases root_cases (stateBefore x (t + 1) w).S with ⟨h, -, -⟩ | ⟨-, h | h⟩
    · exact h
    · rw [hc] at h; cases h
    · exact absurd hm1 h
  left
  refine ⟨hroot, hm1, ?_⟩
  rw [hroot]
  intro hanc
  have hRJ : (get_fc_root (stateBefore x t w).S).AncestorEq (stateBefore x t w).S.J := by
    rcases root_cases (stateBefore x t w).S with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · rw [h1]
      exact ancestorEq_refl _
    · rw [h1]
      exact F_ancestorEq_J_of_stateBefore S Sched x t w
  have h2 := ancestorEq_trans hanc hRJ
  obtain ⟨⟨D', -, hJ', hj'⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (t + 1) w
  obtain ⟨⟨D, -, hJ, hj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  have hh1 : 1 ≤ (chainStateOf S.C D').h_j := by
    unfold Height at *
    omega
  have hJ'h := (chainStateOf_J_spec S.C D').2.2 hh1
  by_cases hj0 : (chainStateOf S.C D).h_j = 0
  · have hg := (chainStateOf_J_spec S.C D).2.1 hj0
    rw [hJ, hg] at h2
    exact hJg ((ancestorEq_genesis_iff _).1 h2)
  · have hJh := (chainStateOf_J_spec S.C D).2.2 (Nat.one_le_iff_ne_zero.mpr hj0)
    rw [hJ', hJ] at h2
    have hle := (lem47_chain_state_heights S.C _ _).2.2.2.1 h2
    rw [hJ'h, hJh] at hle
    unfold Height at *
    omega

/-- **No honest validator reaches the height of a later honest proposal's justification one delay
before it.** When `p` proposes `B` at the start of slot `s + 1`, an honest validator `u` at a time
`t` from `GST` with `t + Δ` at most that start has `h_j` less than `B`'s chain-state height.

Roots name blocks until `slotStart S (s + 1)`: the proposer's `h_j` is read before the start of
slot `s + 1` (`h_j_mono`), after `u`'s justification spreads to it by `t + Δ`. -/
theorem h_j_lt_of_later_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd t s : ℕ) (u p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hGST : GST ≤ t) (hle : t + Δ S ≤ slotStart S (s + 1)) (hEnd : slotStart S (s + 1) ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int))
    (hp : ∀ t' : ℕ, t ≤ t' → t' ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t' : Int) ∧ p ∉ Sched.adv (t' : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    (stateBefore x t u).S.h_j < (chainStateOf S.C B).h := by
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t u
  have h1 := held_spread_h_j S Sched x GST tEnd t t u p D hDiv hMono hSync hCatch
    (hRoots.mono hle) hParent hU hThird le_rfl hGST (by omega) hu hD
    (fun t' h1 h2 => hp t' h1 (by omega))
  have h2 := h_j_mono S Sched x hDiv hMono hU hRoots tEnd (t + Δ S) (slotStart S (s + 1)) p hThird
    hle hEnd (hp _ (by omega) le_rfl).2 le_rfl
  have h3 := honest_proposal_above_h_j S Sched x s B p hPropose
  rw [hj]
  unfold Height at *
  omega

omit [RootOrder] in
/-- A chain state whose justification height is at most `1` has the genesis block as its justified
block: at `0` by `chainStateOf_J_spec`; at `1` the justified block is an entry of height `1`, and the
genesis block, an ancestor of it at the same height, has itself as `T_h`. -/
theorem J_genesis_of_h_j_le_one (C : Config) (D : Block V) (h1 : (chainStateOf C D).h_j ≤ 1) :
    (chainStateOf C D).J = Block.genesis := by
  by_cases h0 : (chainStateOf C D).h_j = 0
  · exact (chainStateOf_J_spec C D).2.1 h0
  · have hh := (chainStateOf_J_spec C D).2.2 (Nat.one_le_iff_ne_zero.mpr h0)
    rcases chainStateOf_J_entry C D with h | h
    · exact h
    · have he := (lem47_chain_state_heights C (Block.genesis : Block V) (chainStateOf C D).J).2.2.2.2
        (genesis_ancestorEq _) (by
          rw [hh, chainStateOf_genesis_h]
          unfold Height at *
          omega)
      rw [h, chainStateOf_genesis_T_h] at he
      exact he.symm

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the
waited height `h`, other than the genesis block.** With `t₀ + Δ` the start of the later opening's
slot `s + 1`, whose honest proposer `p` proposes `B₂` at the height `h`; every honest
`head_height_floor` at most `h` from `t₀` to `tc`; `p` awake and honest from `tL` (at least `GST`)
to the start of slot `s + 1`; and no honest fork-choice change from `t₀` to before `tc`:
every honest validator at a time from `tL` to `tc` has `h_j < h`, or the genesis block as its
justified block.

Roots name blocks until `slotStart S (s + 1)`: `h_j_lt_of_later_proposal` at the later opening's
slot `s + 1`, the only reading of the premise. -/
theorem h_j_lt_or_genesis_before_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd tL t₀ tc s h : ℕ) (p : V) (B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hGST : GST ≤ tL) (hL0 : tL ≤ t₀) (ht₀ : t₀ + Δ S = slotStart S (s + 1))
    (hs : slotStart S (s + 1) ≤ tEnd)
    (hp : ∀ t' : ℕ, tL ≤ t' → t' ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t' : Int) ∧ p ∉ Sched.adv (t' : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hB₂ : (chainStateOf S.C B₂).h = h)
    (hF : ∀ (u : V) (t : ℕ), t₀ ≤ t → t ≤ tc → u ∉ Sched.adv (t : Int) →
      head_height_floor (stateBefore x t u).S ≤ h)
    (hNo : ∀ (w : V) (t' : ℕ), t₀ ≤ t' → t' < tc → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (u : V) (t : ℕ) (hGt : tL ≤ t) (htc' : t ≤ tc) (hu : u ∉ Sched.adv (t : Int)) :
    (stateBefore x t u).S.h_j < h ∨ (stateBefore x t u).S.J = Block.genesis := by
  have hW3 : ∀ t', tL ≤ t' → t' ≤ t₀ → t' ≤ t →
      (stateBefore x t' u).S.h_j < h := by
    intro t' h1 h2 h3
    have hu' : u ∉ Sched.adv ((x[stepBefore x t'].time : ℕ) : Int) := fun hh =>
      hu (hMono _ _ (by exact_mod_cast le_trans (time_stepBefore_le x t') h3) hh)
    have := h_j_lt_of_later_proposal S Sched x GST tEnd t' s u p B₂ hDiv hMono hSync hCatch
      hRoots hParent hU hThird (le_trans hGST h1) (by omega) hs hu'
      (fun t'' h1' h2' => hp t'' (le_trans h1 h1') h2') hPropose
    rw [hB₂] at this
    exact this
  by_cases hlt : (stateBefore x t u).S.h_j < h
  · exact Or.inl hlt
  right
  by_contra hJg
  have htt₀ : t₀ < t := by
    by_contra hle
    exact hlt (hW3 t hGt (by omega) le_rfl)
  -- `h ≥ 2`: a justified block other than the genesis block has a justification height at least 2
  obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t u
  have hj2 : 2 ≤ (stateBefore x t u).S.h_j := by
    by_contra hlt2
    apply hJg
    rw [hJD]
    exact J_genesis_of_h_j_le_one S.C D (by rw [← hjD]; unfold Height at *; omega)
  have hflt := hF u t (by omega) htc' hu
  have hjl := h_j_lt_h_max S Sched x t u
  have hmx := h_max_le_floor_add_one (stateBefore x t u).S
  have hh2 : 2 ≤ h := by
    unfold Height at *
    omega
  -- the first time from `t₀` at which `u`'s `h_j` reaches `h`
  classical
  have hex : ∃ n : ℕ, h ≤ (stateBefore x (t₀ + n) u).S.h_j :=
    ⟨t - t₀, by rw [show t₀ + (t - t₀) = t by omega]; unfold Height at *; omega⟩
  have hn := Nat.find_spec hex
  have hnle : Nat.find hex ≤ t - t₀ :=
    Nat.find_min' hex (by rw [show t₀ + (t - t₀) = t by omega]; unfold Height at *; omega)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hn
    have := hW3 t₀ hL0 le_rfl (by omega)
    unfold Height at *
    omega
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  set t₁ := t₀ + (Nat.find hex - 1) with ht₁
  have ht₁1 : t₀ + Nat.find hex = t₁ + 1 := by omega
  rw [ht₁1] at hn
  have hu₁ : u ∉ Sched.adv ((t₁ + 1 : ℕ) : Int) := fun hh =>
    hu (hMono _ _ (by exact_mod_cast (show t₁ + 1 ≤ t by omega)) hh)
  have hu₁' : u ∉ Sched.adv ((t₁ : ℕ) : Int) := fun hh =>
    hu (hMono _ _ (by exact_mod_cast (show t₁ ≤ t by omega)) hh)
  have hfl₁ := hF u (t₁ + 1) (by omega) (by omega) hu₁
  have hJg₁ : (stateBefore x (t₁ + 1) u).S.J ≠ Block.genesis := by
    intro hg
    obtain ⟨⟨D₁, -, hJD₁, hjD₁⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (t₁ + 1) u
    have hh1 : 1 ≤ (chainStateOf S.C D₁).h_j := by
      rw [← hjD₁]
      unfold Height at *
      omega
    have hJh := (chainStateOf_J_spec S.C D₁).2.2 hh1
    rw [← hJD₁, hg] at hJh
    have : (chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
        chainStateOf_genesis_h S.C
    rw [this, ← hjD₁] at hJh
    unfold Height at *
    omega
  have hch := change_of_h_j_reaches S Sched x u t₁ h (by
    have := hprev
    unfold Height at *
    omega) hn hfl₁ hJg₁
  exact hNo u t₁ (by omega) (by omega) hu₁' hch

end GoldilocksCorrectness.Proofs.Executions
