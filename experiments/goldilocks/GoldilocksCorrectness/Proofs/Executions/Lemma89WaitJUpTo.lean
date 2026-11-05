module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89WaitJ
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo

@[expose] public section

/-!
# `Lemma89WaitJ.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89WaitJ.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `h_j_lt_of_later_proposal`, `h_j_lt_or_genesis_before_cutoff`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (h_max_le_floor_add_one)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_h)

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

/-- **No honest validator reaches the height of a later honest proposal's justification one delay
before it.** When `p` proposes `B` at the start of slot `s + 1`, an honest validator `u` at a time
`t` from `GST` with `t + Δ` at most that start has `h_j` less than `B`'s chain-state height.

Roots name blocks until `slotStart S (s + 1)`: the proposer's `h_j` is read before the start of
slot `s + 1` (`h_j_mono`), after `u`'s justification spreads to it by `t + Δ`.

Restated with the delivery premises up to `slotStart S (s + 1)`: the bound of its roots `hRoots`; the one delivery its proof reads is `held_spread_h_j_upTo` at `t`, due by `t + Δ S`. -/
theorem h_j_lt_of_later_proposal_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd t s : ℕ) (u p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (slotStart S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (slotStart S (s + 1)))
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
  have h1 := held_spread_h_j_upTo S Sched x GST tEnd t t u p D hDiv hMono
    (hSync.mono hle) (hCatch.mono hle) (hRoots.mono hle) hParent hU hThird le_rfl hGST (by omega) hu hD
    (fun t' h1 h2 => hp t' h1 (by omega))
  have h2 := h_j_mono S Sched x hDiv hMono hU hRoots tEnd (t + Δ S) (slotStart S (s + 1)) p hThird
    hle hEnd (hp _ (by omega) le_rfl).2 le_rfl
  have h3 := honest_proposal_above_h_j S Sched x s B p hPropose
  rw [hj]
  unfold Height at *
  omega

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the
waited height `h`, other than the genesis block.** With `t₀ + Δ` the start of the later opening's
slot `s + 1`, whose honest proposer `p` proposes `B₂` at the height `h`; every honest
`head_height_floor` at most `h` from `t₀` to `tc`; `p` awake and honest from `tL` (at least `GST`)
to the start of slot `s + 1`; and no honest fork-choice change from `t₀` to before `tc`:
every honest validator at a time from `tL` to `tc` has `h_j < h`, or the genesis block as its
justified block.

Roots name blocks until `slotStart S (s + 1)`: `h_j_lt_of_later_proposal` at the later opening's
slot `s + 1`, the only reading of the premise.

Restated with the delivery premises up to `slotStart S (s + 1)`: the bound of its roots `hRoots`, as `h_j_lt_of_later_proposal_upTo`, which it calls. -/
theorem h_j_lt_or_genesis_before_cutoff_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd tL t₀ tc s h : ℕ) (p : V) (B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (slotStart S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (slotStart S (s + 1)))
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
    have := h_j_lt_of_later_proposal_upTo S Sched x GST tEnd t' s u p B₂ hDiv hMono hSync hCatch
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

