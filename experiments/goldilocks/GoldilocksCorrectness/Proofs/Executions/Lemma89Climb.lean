module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability

@[expose] public section

/-!
# Lemma 89 on the fast-confirmation route: the threshold and the first round above it

The proofs of B1 to B4 of part B of Lemma 89's skeleton on the fast-confirmation route
, stated in
`GoldilocksCorrectness/Statements/Executions/Lemma89Statements.lean`. Write `a_r := aR S r` for
the action time of round `r`, and `H₂` for the threshold at the time `T₁`
(`OldHeightAttained S Sched x T₁ H₂`). `T₁` is a parameter of each statement; the climb's
assembly takes `T₁ := slotStart S (rs 0 * R − 2k + 1)`.

- `eq_aR_of_honestAttestationAt`: an honest attestation is sent at a round's action time;
- B1 `exists_old_height_attained`: the threshold `H₂` at `T₁` exists;
- B2 `honest_h_max_bounds`: from `T₁ + Δ` to `a_r`, every honest `h_max` is `H₂` or `H₂ + 1`;
- B3 `first_attestation_above_bound`: the first honest attestation above `H₂` from `T₁` on is at a
  round's action time `a_r`, and nothing honest above `H₂` was sent at a tick before `a_r`;
- B4 `fast_block_at_first_round`: its sender holds a fast block of height exactly `H₂ + 1`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_succ_times)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem49_tick_attests expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- An honest attestation is sent at the action time of a round: when `v`, honest and awake at `t`,
put the attestation `a` on the wire at its tick then, `t` is `aR S r` for some round `r`.

Why: the tick's attestation is the duty's (Lemma 49), so `t` is the action time of the round of
its slot, which is the support cutoff of that round's second slot (`supportCutoff_succ_times`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time of the tick; `v`: the
  attester; `a`: the attestation. -/
theorem eq_aR_of_honestAttestationAt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (a : Attestation V)
    (hSend : HonestAttestationAt S Sched x t v a) :
    ∃ r : ℕ, t = aR S r := by
  obtain ⟨i, hl, -, -, hSent⟩ := hSend
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hSent
  obtain ⟨hT, -⟩ := lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  refine ⟨S.C.round (S.C.slot (t : Int)), ?_⟩
  obtain ⟨hslot, hround, hcut, -⟩ :=
    supportCutoff_succ_times S (S.C.round (S.C.slot (t : Int)))
      (S.C.round (S.C.slot (t : Int)) * S.C.R) rfl
  rw [hslot, hround] at hcut
  have h : ((t : ℕ) : Int) = ((aR S (S.C.round (S.C.slot (t : Int))) : ℕ) : Int) :=
    hT.trans hcut.symm
  exact_mod_cast h

/-- **B1, the threshold exists.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: every honest attestation sent at a tick before `T₁` is in the sent log of the
configuration `x[stepBefore x T₁]` (`lt_stepBefore_iff`, `sent_le_of_le`), so the heights of these
attestations are bounded; `H₂` is the least bound (`Nat.find`), which is `0` or attained: a least
bound `H₂ > 0` that no such attestation reached would leave `H₂ − 1` a bound.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time. -/
theorem exists_old_height_attained (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (T₁ : ℕ)
    (hDiv : TimeDiverges x.toTrace) :
    ∃ H₂ : ℕ, OldHeightAttained S Sched x T₁ H₂ := by
  classical
  let Hs : Set ℕ := {h | ∃ (t : ℕ) (v : V) (a : Attestation V), t < T₁ ∧
    HonestAttestationAt S Sched x t v a ∧ a.h = h}
  let f : SignedMsg V (NamedObject V) → ℕ := fun sm =>
    match sm.msg with
    | .attest a => a.h
    | _ => 0
  have hbdd : ∃ B : ℕ, ∀ h ∈ Hs, h ≤ B := by
    refine ⟨((x[stepBefore x T₁].sent).map f).sup, ?_⟩
    rintro h ⟨t, v, a, ht, ⟨i, hl, -, -, hm⟩, rfl⟩
    have hm1 : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) hm
    have hi : i < stepBefore x T₁ := by
      rw [lt_stepBefore_iff x hDiv, (time_of_lbl_tickAllAwake x hl).2]
      exact ht
    have hm2 := Multiset.mem_of_le (sent_le_of_le x (show i + 1 ≤ stepBefore x T₁ by omega)) hm1
    exact Multiset.le_sup (Multiset.mem_map_of_mem f hm2)
  -- the least upper bound of the heights attested before `T₁`
  refine ⟨Nat.find hbdd, ?_, ?_⟩
  · intro i t v a hl ht hAw hHon hm
    exact Nat.find_spec hbdd a.h ⟨t, v, a, ht, ⟨i, hl, hAw, hHon, hm⟩, rfl⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hbdd) with h0 | hpos
    · exact Or.inl h0
    · right
      by_contra hno
      refine Nat.find_min hbdd (show Nat.find hbdd - 1 < Nat.find hbdd by omega) ?_
      intro h hh
      have hle := Nat.find_spec hbdd h hh
      have hne : h ≠ Nat.find hbdd := by
        rintro rfl
        obtain ⟨t, v, a, ht, hA, hah⟩ := hh
        exact hno ⟨t, v, a, ht, hA, hah⟩
      omega

/-- **B2, the honest `h_max` from `T₁ + Δ` to `a_r`.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: at least `H₂` by `lem89b_at` (Lemma 89b on the four facts its proof reads) at the
honest attestation of height `H₂` sent before `T₁`, when `H₂ ≠ 0`; at most `H₂ + 1` because
`h_max` is the chain-state height of a block `w` holds (`cachesWitnessed_of_stateBefore`) and A2
bounds every such block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the time of the
  threshold; `r`: the round; `H₂`: the threshold; `t`: the time; `w`: the validator.

Roots name blocks until `t`: the proof reads `lem89b_at` at `b := t`, `w`'s reading time. -/
theorem honest_h_max_bounds (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ t : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (ht₁ : T₁ + Δ S ≤ t) (htr : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ ≤ (stateBefore x t w).S.h_max ∧ (stateBefore x t w).S.h_max ≤ H₂ + 1 := by
  refine ⟨?_, ?_⟩
  · rcases hH₂.2 with h0 | ⟨t', u, a, ht', ⟨i, hl, -, -, hm⟩, hah⟩
    · rw [h0]
      exact Nat.zero_le _
    · rw [← hah]
      have hΔ := one_le_Δ S
      refine lem89b_at S Sched x GST t t' i t u w a hDiv hMono
        (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
        (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hU (by omega)
        (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast (show t ≤ tAwakeEnd by omega))
          hThird) (by omega) ?_ ⟨hl, hm⟩ le_rfl
      intro t'' h1 h2
      have hwt : w ∉ Sched.adv (t'' : Int) := fun h => hw (hMono _ _ (by omega) h)
      exact ⟨hAwake t'' (by omega) (by omega) w hwt, hwt⟩
  · obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
    rw [← hXh]
    exact held_height_le_before_action S Sched x tAwakeEnd r H₂ t w X hU hThird hOld htr hEnd hX

/-- **B3, the first honest attestation above `H₂`.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: the least time `t ≥ T₁` with an honest attestation above `H₂` (`Nat.find`) is at most
`t₀` and is a round's action time (`eq_aR_of_honestAttestationAt`); every honest attestation at a
tick before it is at most `H₂`, before `T₁` by `OldHeightAttained`, from `T₁` on by the
minimality.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time of the threshold;
  `H₂`: the threshold; `t₀`: the time of the given attestation; `u`: its sender; `a₀`: the
  attestation. -/
theorem first_attestation_above_bound (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (T₁ H₂ t₀ : ℕ) (u : V) (a₀ : Attestation V)
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (ht₀ : T₁ ≤ t₀) (hSend : HonestAttestationAt S Sched x t₀ u a₀) (ha₀ : H₂ < a₀.h) :
    ∃ r : ℕ, T₁ ≤ aR S r ∧ aR S r ≤ t₀ ∧ OldAttestationsAtMost S Sched x (aR S r) H₂ ∧
      ∃ (v : V) (a : Attestation V), HonestAttestationAt S Sched x (aR S r) v a ∧ H₂ < a.h := by
  classical
  have hP : ∃ t : ℕ, T₁ ≤ t ∧ ∃ (v : V) (a : Attestation V),
      HonestAttestationAt S Sched x t v a ∧ H₂ < a.h := ⟨t₀, ht₀, u, a₀, hSend, ha₀⟩
  obtain ⟨hT, v, a, hA, ha⟩ := Nat.find_spec hP
  obtain ⟨r, hr⟩ := eq_aR_of_honestAttestationAt S Sched x _ v a hA
  have hle : Nat.find hP ≤ t₀ := Nat.find_min' hP ⟨ht₀, u, a₀, hSend, ha₀⟩
  refine ⟨r, ?_, ?_, ?_, v, a, ?_, ha⟩
  · rw [← hr]; exact hT
  · rw [← hr]; exact hle
  · intro i t w b hl ht hAw hHon hm
    by_cases hlt : t < T₁
    · exact hH₂.1 i t w b hl hlt hAw hHon hm
    · by_contra hgt
      exact Nat.find_min hP (show t < Nat.find hP by rw [hr]; exact ht)
        ⟨Nat.le_of_not_lt hlt, w, b, ⟨i, hl, hAw, hHon, hm⟩, Nat.lt_of_not_le hgt⟩
  · rw [← hr]; exact hA

/-- **B4, the fast block at the first round above the threshold.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: A1 gives the fast block `L` of `v`'s update at `a_r`, held by `v` before `a_r`, with
`h(L) = a.h > H₂`; A2 at `t := a_r` bounds `h(L) ≤ H₂ + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end; `r`:
  the round; `H₂`: the threshold; `v`: the attester; `a`: the attestation. -/
theorem fast_block_at_first_round (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ : ℕ) (v : V) (a : Attestation V)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂) (hEnd : aR S r ≤ tAwakeEnd)
    (hSend : HonestAttestationAt S Sched x (aR S r) v a) (ha : H₂ < a.h) :
    ∃ (A' : ACState V) (L : Block V),
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A' ∧
      L ∈ A'.fast_blocks ∧ L ∈ (stateBefore x (aR S r) v).S.T ∧
      (chainStateOf S.C L).h = H₂ + 1 := by
  obtain ⟨A', L, hUpd, hFast, hLv, hLh⟩ := fast_block_of_honest_attestation S Sched x r v a hSend
  have hle := held_height_le_before_action S Sched x tAwakeEnd r H₂ (aR S r) v L hU hThird hOld
    (le_refl _) hEnd hLv
  refine ⟨A', L, hUpd, hFast, hLv, ?_⟩
  unfold Height at *
  omega

end GoldilocksCorrectness.Proofs.Executions
