module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma32
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# Lemma 89 on the fast-confirmation route: the base at the slot after the fast block's round

The proof of A5 `fast_block_base` of Lemma 89's skeleton on the fast-confirmation route
, stated in
`GoldilocksCorrectness/Statements/Executions/Lemma89Statements.lean`, and the kit facts it reads.
Write `s₀ := r * R`, `a_r := aR S r`, the support cutoff of slot `s₀ + 1`, and `L` for the fast
block of `v`'s update at `a_r`, at the chain-state height `H₂ + 1`:

- `fc_root_ancestorEq_of_tall`: an FG state that holds `L` at its `h_max`, on its finalized
  block's chain, has its fork-choice root `L` or an ancestor of `L` (the contest rule);
- `live_locks_compatible_of_clauses`, `locks_step_of_clauses`: the live-lock kit theorem and
  Lemma 79b, from weaker facts of the earlier slot (the saved confirmation compatible with the
  block, in place of a descendant of it);
- `finalized_compatible_fast_block`: up to the support cutoff of slot `s₀ + 2`, every honest
  finalized block is compatible with `L`;
- A5 `fast_block_base`: the slot invariant restricted to `L` at slot `s₀ + 1`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_le_voteTime dutyWindowStart_mono dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_cast
  voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_ancestorEq_of_tall floor_le_h_max
  mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fc_root_eq is_live_iff pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotes expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible revoke_locks_entry_mem_tree)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The live locks of `w` are compatible with `B`, from the two facts of slot `s'` the proof of
`live_locks_compatible_of_honestChainExtends` reads, in a weaker form: every live entry of `w`'s
revocation of slot `s' + 1` is compatible with `B`, and every confirmation of slot `s'` that `w`'s
update of slot `s' + 1` saves is compatible with `B` (in place of `B` or a descendant of `B`).

Why: `live_locks_compatible_of_honestChainExtends`'s proof; in the case of an entry of slot `s'`,
the entry's block is the saved confirmation or an ancestor of it, so compatible with `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the block; `s'`: the slot;
  `t`: the time; `w`: the validator. -/
theorem live_locks_compatible_of_clauses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (B : Block V) (s' t : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hL2 : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 1)) w).A
        ((voteTime S (s' + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
        ((voteTime S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
          ((voteTime S (s' + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hL3 : ∀ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s' + 1)) w).A
          ((supportCutoff S (s' + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) w).S)
        ((supportCutoff S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' →
      ∀ C' : Block V, A'.saved_confirmation s' = some C' → C'.compatible B = true)
    (hHon : ∀ t'' : ℕ, dutyWindowStart S (s' + 2) ≤ t'' → t'' ≤ t →
      w ∈ Sched.awake (t'' : Int) ∧ w ∉ Sched.adv (t'' : Int))
    (ht1 : supportCutoff S (s' + 1) < t)
    (ht2 : t ≤ voteTime S (s' + 2)) :
    ∀ e ∈ (stateBefore x t w).A.lock_entries, ((t : ℕ) : Int) < e.d →
      e.B.compatible B = true := by
  intro e he hlive
  have hΔ := one_le_Δ S
  have hv' : ∀ s : ℕ, voteTime S s = slotStart S s + Δ S := voteTime_eq S
  have hc' : ∀ s : ℕ, supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S
  have hss : ∀ s : ℕ, slotStart S (s + 1) = slotStart S s + 4 * Δ S := fun s => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  obtain ⟨s₁, hd₁, hcut₁, hτ₁, A', hA', e₀, -, -, -, -, ⟨C', hC', hBC⟩, -, htr⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem39_lock_entry_provenance S Sched x t w e hDiv he
  obtain ⟨e₁, -, -, hB₁, hB₁₀⟩ := htr t hcut₁ le_rfl
  have heC : e.B.AncestorEq C' := ancestorEq_trans (ancestorEq_trans hB₁ hB₁₀) hBC
  have hs₁ : s₁ ≤ s' := by
    by_contra h
    have hm := slotStart_mono S (show s' + 2 ≤ s₁ + 1 by omega)
    have h1 := hv' (s' + 2)
    have h2 := hc' (s₁ + 1)
    have h3 := hv' (s₁ + 1)
    omega
  rcases Nat.lt_or_eq_of_le hs₁ with hlt | heq
  · have hk : s' + 1 ≤ s₁ + S.C.k := by
      by_cases hkle : S.C.k ≤ s' + 1
      · have h41 := GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
          (s' + 1 - S.C.k) s₁ t e hd₁ hlive (by
            rw [show s' + 1 - S.C.k + S.C.k = s' + 1 by omega]
            have := hc' (s' + 1)
            omega)
        omega
      · omega
    have hdw : dutyWindowStart S (s' + 2) ≤ supportCutoff S (s₁ + 1) :=
      dutyWindowStart_le_supportCutoff S (by omega)
    have hc₃ : supportCutoff S (s₁ + 1) ≤ voteTime S (s' + 1) := by
      have hm := slotStart_mono S (show s₁ + 1 ≤ s' by omega)
      have h1 := hc' (s₁ + 1)
      have h2 := hv' (s₁ + 1)
      have h3 := hv' (s' + 1)
      have h4 := hss s'
      omega
    have ht₃ : voteTime S (s' + 1) < t := by
      have := hc' (s' + 1)
      omega
    have hv₃ := hv' (s' + 1)
    obtain ⟨hl₃, -, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s' + 1))
    have hw₃ := hHon (voteTime S (s' + 1)) (by omega) (by omega)
    obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hw₃.1 hw₃.2
    have hslot₃ : S.C.slot ((voteTime S (s' + 1) : ℕ) : Int) = s' + 1 := by
      have := hv' (s' + 1)
      have := hss (s' + 1)
      exact slot_eq_of_mem S (by omega) (by omega)
    obtain ⟨τ, hτ, hτle⟩ := hτ₁
    have hAw₃ : (tickInputState x (stepBefore x (voteTime S (s' + 1))) (voteTime S (s' + 1))
        w).awakeSince = some τ :=
      GoldilocksCorrectness.Statements.Executions.awakeSince_kept_of_awake_throughout S Sched x _ _
        w τ hDiv hc₃ hτ (fun t'' h1 h2 => (hHon t'' (by omega) (by omega)).1)
    have hτ₃ : τ ≤ duty_window_start S.C (s' + 1) :=
      le_trans hτle (duty_window_start_mono S (by omega))
    have hA₃ : (tickInputState x (stepBefore x (voteTime S (s' + 1))) (voteTime S (s' + 1)) w).A =
        (stateBefore x (voteTime S (s' + 1)) w).A := (tickInputState_frame x _ _ w).2.1
    have hS₃ : (tickInputState x (stepBefore x (voteTime S (s' + 1))) (voteTime S (s' + 1)) w).S =
        (stateBefore x (voteTime S (s' + 1)) w).S := (tickInputState_frame x _ _ w).1
    obtain ⟨A₃, hRevoke, hlock₃⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
        hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact ⟨τ, hAw₃, hτ₃⟩)
    rw [hslot₃, hA₃, hS₃] at hRevoke
    have hkeep := stateBefore_succ_keepsConfirmation x hDiv w hti₃'
    rw [hst₃] at hkeep
    obtain ⟨k1, -, -, -⟩ := hkeep
    obtain ⟨e', he', hd', heB', -⟩ := htr (voteTime S (s' + 1) + 1) (by omega) (by omega)
    rw [k1, hlock₃] at he'
    have hlive' : is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
        ((voteTime S (s' + 1) : ℕ) : Int) e' = true := by
      rw [is_live_iff]
      refine ⟨?_, revoke_locks_entry_mem_tree (Nat.le_add_left 1 s') hRevoke e' he'⟩
      rw [hd']
      exact lt_trans (Int.ofNat_lt.2 ht₃) hlive
    exact compatible_of_ancestorEq_compatible heB' (hL2 A₃ hRevoke e' he' hlive')
  · subst heq
    exact compatible_of_ancestorEq_compatible heC (hL3 A' hA' C' hC')

/-- The second clause of the slot invariant restricted to `B` at slot `s' + 1`, from the weaker
facts of slot `s'` of `live_locks_compatible_of_clauses`: Lemma 79b's proof.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the block; `s'`: the slot;
  `w`: the validator. -/
theorem locks_step_of_clauses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (B : Block V) (s' : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hL2 : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 1)) w).A
        ((voteTime S (s' + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
        ((voteTime S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
          ((voteTime S (s' + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hL3 : ∀ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s' + 1)) w).A
          ((supportCutoff S (s' + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) w).S)
        ((supportCutoff S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' →
      ∀ C' : Block V, A'.saved_confirmation s' = some C' → C'.compatible B = true)
    (hHon : ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ voteTime S (s' + 2) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int)) :
    ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 2)) w).A
        ((voteTime S (s' + 2) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
        ((voteTime S (s' + 2) : ℕ) : Int) (s' + 2) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
          ((voteTime S (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro A' hRevoke e' he' _
  have hΔ := one_le_Δ S
  have hv₂ : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hc₁ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hlt₂ : supportCutoff S (s' + 1) < voteTime S (s' + 2) := by omega
  obtain ⟨e, he, -, -, hB, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _ _ (s' + 2)
      (Nat.le_add_left 1 (s' + 1)) hRevoke e' he'
  obtain ⟨heS, hlt⟩ := Finset.mem_filter.1 he
  exact compatible_of_ancestorEq_compatible hB
    (live_locks_compatible_of_clauses S Sched x B s' (voteTime S (s' + 2)) w hDiv hL2 hL3
      hHon hlt₂ le_rfl e heS hlt)

/-- **Kit fact, the honest finalized blocks up to the support cutoff of slot `s₀ + 2` are
compatible with the fast block.** Under the execution assumptions, unforgeability and fewer than a
third of the validators in the adversary set up to `tAwakeEnd`: when every honest attestation sent
before the support cutoff of slot `s₀ + 1` has height at most `H₂`; `v`, honest then and awake and
honest from the support cutoff to the view freeze of slot `s₀`, has its update of slot `s₀ + 1` save
`C'`, with `L` an ancestor of `C'` or `C'`; `v` holds `L` before that cutoff, at the height `H₂ + 1`;
and `w` is honest at a time `t ≥ 1` at most the support cutoff of slot `s₀ + 2` — then `w`'s
finalized block before `t` is compatible with `L`.

Why: `w`'s finalized block is the finalized block of the chain state of a block `D` it holds. At a
finalization height at most `H₂`, Lemma 89a with `v` holding `L` makes it an ancestor of `L`.
Above `H₂`, it is justified on `D`'s chain (Lemma 66), and its certificate names an entry `E` of the
honest chain at a slot whose update ran before `t`, so at slot `s₀` (`cert_entry_at_slot`): `E` is
an updater's confirmation of slot `s₀` or an ancestor of it, compatible with `C'` (Lemma 31); the
finalized block is `E` (roots name blocks).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tAwakeEnd`: the phase's end; `s₀`: the first slot of the round; `H₂`:
  the bound on the old attestations; `t`: the time; `v`: the validator whose update saves `C'`;
  `w`: the validator whose finalized block is read; `L`: the block; `C'`: the saved confirmation;
  `A'`: the update's answer.

Roots name blocks until `max t (supportCutoff S (s₀ + 1))`: the proof compares (Lemma 89a) a
block `w` holds before `t` with `L`, which `v` holds before the support cutoff of slot `s₀ + 1`,
and, past `H₂`, `w`'s finalized block with the entry of the honest chain at slot `s₀`, held by
that cutoff (Lemma 31 at slot `s₀`). -/
theorem finalized_compatible_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tAwakeEnd s₀ H₂ t : ℕ) (v w : V) (L C' : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (max t (supportCutoff S (s₀ + 1))))
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H₂)
    (hGST : GST ≤ supportCutoff S s₀)
    (hEnd : supportCutoff S (s₀ + 2) ≤ tAwakeEnd)
    (hvw : ∀ t' : ℕ, supportCutoff S s₀ ≤ t' → t' ≤ viewFreeze S s₀ →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    (hv : v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s₀ + 1)) v).A
          ((supportCutoff S (s₀ + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S)
        ((supportCutoff S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A')
    (hSaved : A'.saved_confirmation s₀ = some C')
    (hLC : L.AncestorEq C')
    (hLv : L ∈ (stateBefore x (supportCutoff S (s₀ + 1)) v).S.T)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (ht1 : 1 ≤ t) (ht : t ≤ supportCutoff S (s₀ + 2)) (hw : w ∉ Sched.adv (t : Int)) :
    (stateBefore x t w).S.F.compatible L = true := by
  have hΔ := one_le_Δ S
  obtain ⟨D, hD, hFD⟩ :=
    GoldilocksCorrectness.Statements.Executions.finalizedFromChain_of_exec S Sched x
      (stepBefore x t) w
  show (x[stepBefore x t][w].st).S.F.compatible L = true
  rw [hFD]
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have htv : x[stepBefore x (supportCutoff S (s₀ + 1))].time ≤ supportCutoff S (s₀ + 1) :=
    time_stepBefore_le x _
  have hcc12 : supportCutoff S (s₀ + 1) ≤ supportCutoff S (s₀ + 2) := supportCutoff_mono S (by omega)
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (hMono _ _ (by exact_mod_cast htj.le) h)
  have hv' : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (s₀ + 1))].time : Int) :=
    fun h => hv (hMono _ _ (by exact_mod_cast htv) h)
  by_cases hle : (chainStateOf S.C D).h_F ≤ H₂
  · have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
        (max (x[stepBefore x t].time : Int)
          (x[stepBefore x (supportCutoff S (s₀ + 1))].time : Int)) :=
      adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show
        x[stepBefore x t].time ≤ tAwakeEnd by omega)) (by exact_mod_cast (show
        x[stepBefore x (supportCutoff S (s₀ + 1))].time ≤ tAwakeEnd by omega))) hThird
    have hFL := lem68_honest_past_finalized S Sched x hU hRoots (stepBefore x t)
      (stepBefore x (supportCutoff S (s₀ + 1))) w v D L hT hw' hv' hD hLv
      (by rw [hL]; exact Nat.lt_succ_of_le hle) (max_le_max htj.le htv)
    exact (compatible_iff _ _).2 (Or.inl hFL)
  · have hlt : H₂ < (chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ := (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
      (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (chainStateOf S.C D).F ∈ (x[stepBefore x t][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w D _ hD hFanc
    have hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[stepBefore x t].time : Int) :=
      fewerThanQuorum_of_fewerThanThird Sched _ (adversaryFewerThanThirdUntil_of_le
        (by exact_mod_cast (show x[stepBefore x t].time ≤ tAwakeEnd by omega)) hThird)
    obtain ⟨s_a, E, hcut, hAt, -, -, hEr⟩ := cert_entry_at_slot S Sched x s₀ H₂ (stepBefore x t) w
      D _ _ hDiv hMono hU hAdvQ hOld hD (progressCertOn_of_justificationCertOn hJC) hlt
    obtain ⟨hs₀a, u, hu, Cu, hCu, hECu⟩ := hAt
    have hsa : s_a = s₀ := by
      by_contra hne
      have h2 : supportCutoff S (s₀ + 2) ≤ supportCutoff S (s_a + 1) :=
        supportCutoff_mono S (by omega)
      omega
    subst hsa
    have hFE : (chainStateOf S.C D).F = E :=
      hRoots _ _ ⟨stepBefore x t, w, hw', le_trans htj.le (le_max_left _ _), hFT⟩
        (onHonestChainAt_inHonestTreeBy S Sched x hMono s_a s_a _ E ⟨hs₀a, u, hu, Cu, hCu, hECu⟩
          (le_max_right _ _)) hEr
    have huw := updaterAt_window S Sched s_a u hMono hu
    have hdw : dutyWindowStart S (s_a + 1) ≤ slotStart S s_a := dutyWindowStart_succ_le_slotStart S s_a
    have hv₁ := voteTime_eq S s_a
    have hc₁ := supportCutoff_eq S s_a
    have hf₁ := viewFreeze_eq S s_a
    have hv₂ := voteTime_eq S (s_a + 1)
    have hc₂ := supportCutoff_eq S (s_a + 1)
    have hss : slotStart S (s_a + 1) = slotStart S s_a + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    obtain ⟨Au, hUu, hSu⟩ := update_of_saved_confirmation S Sched x s_a u Cu hDiv hMono huw
      hCu
    have hcc := lem31_saved_confirmations_compatible S Sched x GST s_a u v Au A' Cu C' hDiv hMono
      hSync hCatch (hRoots.mono (le_max_right _ _)) hGST
      (fun t' h1 h2 => huw t' (by omega) (by omega)) hvw
      (huw (supportCutoff S (s_a + 1)) (by omega) le_rfl).2 hv hUu hSu hUpdate hSaved
    rw [hFE]
    exact compatible_of_ancestorEq_both hECu hLC hcc

/-- **A5, the slot invariant restricted to `L` at slot `r * R + 1`.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route, with `s₀ := r * R`: `v`'s update saves a confirmation `C'` of slot `s₀` with `L` an
ancestor of it or it (`update_confirmation_fast_block_saved`), and Lemma 36 at `L` gives the early
supporters `Sup`, not empty by the eligibility test. At every member `w` (honest at the support
cutoff of slot `s₀ + 2`): `w`'s finalized block before the vote time of slot `s₀ + 1` is an
ancestor of `L` (A3); Lemma 63 puts a descendant of `L`, so `L`, in `w`'s tree before the view
freeze of slot `s₀`; so `w`'s `h_max` is `H₂ + 1` (A2 bounds it, `L` reaches it), and its root is
an ancestor of `L` (`fc_root_ancestorEq_of_tall`); `L` is in its voter tree and a viable head
(`proposal_viable_head_at`); Lemma 42 makes its locks compatible with `L`; A4 gives the votes. The
live locks of slot `s₀ + 1`: `locks_step_of_clauses`, with Lemma 42 for the entries of earlier
slots and Lemma 31 for `w`'s confirmation of slot `s₀`. The confirmations: Lemma 79c, with the
honest committee members of slot `s₀ + 1` among the members, and `finalized_compatible_fast_block`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `A'`: the update's answer.

Roots name blocks until `supportCutoff S (r * S.C.R + 2)`: `finalized_compatible_fast_block` at
the support cutoff of slot `r * R + 2`, for the confirmations of slot `r * R + 1`; the other
steps read up to the support cutoff of slot `r * R + 1`. -/
theorem fast_block_base (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (r * S.C.R + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hEnd : supportCutoff S (r * S.C.R + 2) ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1) :
    HonestChainExtends S Sched x (Hon S Sched (r * S.C.R + 1)) L (r * S.C.R + 1) := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℕ, s₀ = r * S.C.R := ⟨_, rfl⟩
  have haR : aR S r = supportCutoff S (s₀ + 1) := by rw [hs₀]; rfl
  rw [← hs₀] at hAnchor hEnd hUpdate hRoots ⊢
  rw [haR] at hUpdate
  have hOld' : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H₂ := by
    rw [← haR]; exact hOld
  have hv' : v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by rw [← haR]; exact hv
  -- the times
  have hΔ := one_le_Δ S
  have hss₀ : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss₁ : slotStart S (s₀ + 2) = slotStart S (s₀ + 1) + 4 * Δ S := by
    show slotStart S (s₀ + 1 + 1) = _
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hv₀ := voteTime_eq S s₀
  have hc₀ := supportCutoff_eq S s₀
  have hf₀ := viewFreeze_eq S s₀
  have hv₁ := voteTime_eq S (s₀ + 1)
  have hc₁ := supportCutoff_eq S (s₀ + 1)
  have hv₂ := voteTime_eq S (s₀ + 2)
  have hc₂ := supportCutoff_eq S (s₀ + 2)
  have hdwA : tGAT + Δ S ≤ dutyWindowStart S s₀ := dutyWindowStart_of_anchor S tGAT s₀ hAnchor
  have hdw0 : dutyWindowStart S s₀ ≤ voteTime S s₀ := dutyWindowStart_le_voteTime S s₀
  have hdw01 : dutyWindowStart S s₀ ≤ dutyWindowStart S (s₀ + 1) :=
    dutyWindowStart_mono S (Nat.le_succ s₀)
  have hdw12 : dutyWindowStart S (s₀ + 1) ≤ dutyWindowStart S (s₀ + 2) :=
    dutyWindowStart_mono S (Nat.le_succ (s₀ + 1))
  have hdw1 : dutyWindowStart S (s₀ + 1) ≤ slotStart S s₀ := dutyWindowStart_succ_le_slotStart S s₀
  -- the windows
  have hHonW : ∀ u : V, u ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) →
      ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s₀ + 2) →
        u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
    intro u hu t h1 h2
    have hut : u ∉ Sched.adv (t : Int) := fun h => hu (hMono _ _ (by exact_mod_cast h2) h)
    exact ⟨hAwake t h1 (le_trans h2 hEnd) u hut, hut⟩
  have hVW : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s₀ + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hut : v ∉ Sched.adv (t : Int) := fun h => hv' (hMono _ _ (by exact_mod_cast h2) h)
    exact ⟨hAwake t h1 (by omega) v hut, hut⟩
  have hmem : ∀ w ∈ Hon S Sched (s₀ + 1), w ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) := by
    intro w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  have hEndR : aR S r ≤ tAwakeEnd := by rw [haR]; omega
  -- `v`'s saved confirmation, and the early supporters of `L` (Lemma 36)
  obtain ⟨C', hSaved, hLC'⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved S.C S.P _ A' _ _
      (s₀ + 1) L (Nat.le_add_left 1 s₀) hUpdate hFast
  rw [Nat.add_sub_cancel] at hSaved
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s₀ + 1) C' L (Nat.le_add_left 1 s₀) hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s₀ v hDiv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) hLC'
  simp only [Nat.add_sub_cancel] at hSup hElig
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s₀ + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S) s₀ L u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  have hElig' : voters_count ((stateBefore x (supportCutoff S (s₀ + 1)) v).A.pool s₀) <
      2 * Sup.card := by rwa [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hElig
  obtain ⟨u₀, hu₀⟩ : Sup.Nonempty := Finset.card_pos.1 (by omega)
  -- `v` holds `L` before the action time
  have hLv' : L ∈ (stateBefore x (supportCutoff S (s₀ + 1)) v).S.T := by
    obtain ⟨vote₀, -, -, ⟨H₀, hH₀, -, hLH₀⟩, -, -⟩ := hSup' u₀ hu₀
    exact ancestors_mem_T_of_exec S Sched x _ v H₀ L ((mem_fg_to_ac_tree _ _).1 hH₀).1 hLH₀
  have hLv : L ∈ (stateBefore x (aR S r) v).S.T := by rw [haR]; exact hLv'
  have hSupAt : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x (supportCutoff S (s₀ + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S) ((supportCutoff S s₀ : ℕ) : Int)
      s₀ L u := by
    intro u hu
    rw [supportCutoff_cast]
    exact hSup' u hu
  -- each member: its finalized block, `L` held, its root
  have hFw : ∀ w : V, w ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) →
      (stateBefore x (voteTime S (s₀ + 1)) w).S.F.AncestorEq L := fun w hw =>
    finalized_ancestor_of_fast_block S Sched x tAwakeEnd r H₂ (voteTime S (s₀ + 1)) v w L hMono
      hU (hRoots.mono (by rw [haR]; exact supportCutoff_mono S (by omega))) hThird hOld hEndR hv hLv
      hL (by rw [haR]; omega)
      (hHonW w hw _ (by omega) (by omega)).2
  have hLw : ∀ w : V, w ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) →
      L ∈ (stateBefore x (viewFreeze S s₀) w).S.T := by
    intro w hw
    obtain ⟨h63, -⟩ := GoldilocksCorrectness.Statements.Executions.lem63_supporters_counted_at S
      Sched x GST s₀ (supportCutoff S s₀) (viewFreeze S s₀) (voteTime S (s₀ + 1))
      (supportCutoff S (s₀ + 1)) (supportCutoff S (s₀ + 1)) Sup L v w hDiv hMono
      (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
      (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch)
      (hRoots.mono (supportCutoff_mono S (by omega))) hParent
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun t h1 h2 => hHonW w hw t (by omega) (by omega))
      (fun t h1 h2 => hVW t (by omega) (by omega)) hSupAt (hFw w hw) (by omega)
    obtain ⟨-, -, -, -, ⟨H_u, hHu, -, hLH, -, -⟩, -⟩ := h63 u₀ hu₀
    exact ancestors_mem_T_of_exec S Sched x _ w H_u L hHu hLH
  have hTall : ∀ w : V, w ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) →
      L ∈ (stateBefore x (voteTime S (s₀ + 1)) w).S.T ∧
      (stateBefore x (voteTime S (s₀ + 1)) w).S.σ L = chainStateOf S.C L ∧
      (chainStateOf S.C L).h = (stateBefore x (voteTime S (s₀ + 1)) w).S.h_max := by
    intro w hw
    have hLT := (stateBefore_grows x hDiv w
      (show viewFreeze S s₀ ≤ voteTime S (s₀ + 1) by omega)).1 (hLw w hw)
    have hInv := (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s₀ + 1))) w).1
    have hσ : (stateBefore x (voteTime S (s₀ + 1)) w).S.σ L = chainStateOf S.C L :=
      hInv.2.2.2.2.2.1 L hLT
    have hge : (chainStateOf S.C L).h ≤ (stateBefore x (voteTime S (s₀ + 1)) w).S.h_max := by
      have h' : ((stateBefore x (voteTime S (s₀ + 1)) w).S.σ L).h ≤
          (stateBefore x (voteTime S (s₀ + 1)) w).S.h_max := hInv.2.2.2.2.2.2.2.2.2.1.2.1.2 L hLT
      rw [hσ] at h'
      exact h'
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x (voteTime S (s₀ + 1)) w
    have hle := held_height_le_before_action S Sched x tAwakeEnd r H₂ (voteTime S (s₀ + 1)) w X
      hU hThird hOld (by rw [haR]; omega) hEndR hX
    refine ⟨hLT, hσ, le_antisymm hge ?_⟩
    rw [hL, ← hXh]
    exact hle
  have hRootL : ∀ w : V, w ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) →
      (get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S).AncestorEq L := fun w hw =>
    fc_root_ancestorEq_of_tall _ L (hTall w hw).1 (hFw w hw)
      (by rw [(hTall w hw).2.1]; exact (hTall w hw).2.2)
  -- Lemma 42 at each member
  have hL42 : ∀ w : V, w ∉ Sched.adv ((supportCutoff S (s₀ + 2) : ℕ) : Int) →
      ∀ A'' : ACState V,
        revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1)) w).A
          ((voteTime S (s₀ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
          ((voteTime S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A'' →
        ∀ e ∈ A''.lock_entries, e.B.compatible L = true := fun w hw =>
    GoldilocksCorrectness.Statements.Executions.lem42_fast_lock_clears_conflicting_locks S Sched x
      GST s₀ L v w A' hDiv hMono hSync hCatch (hRoots.mono (supportCutoff_mono S (by omega)))
      hParent (by omega)
      (fun t h1 h2 => hVW t (by omega) h2) (fun t h1 h2 => hHonW w hw t (by omega) (by omega))
      hUpdate hFast ((compatible_iff _ _).2 (Or.inl (hFw w hw)))
  -- the first clause: the votes of slot `s₀ + 1` (A4 at each member)
  have hVotes : ∀ u ∈ Hon S Sched (s₀ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s₀ + 1)) u).S.T,
        vote = GoldfishVote.mk u (s₀ + 1) H_u.root ∧ L.AncestorEq H_u := by
    intro w hwH vote hSend
    have hw := hmem w hwH
    refine lem36c_fast_ancestor_extended_held S Sched x GST s₀ C' L v w A' vote hDiv hMono hSync
      hCatch (hRoots.mono (supportCutoff_mono S (by omega))) hParent (by omega)
      (fun t h1 h2 => hVW t (by omega) h2)
      (fun t h1 h2 => hHonW w hw t (by omega) (by omega)) hUpdate hSaved hLC'
      ((compatible_iff _ _).2 (Or.inl (by rw [fc_root_eq]; exact hRootL w hw))) ?_
      (fun A'' hR e he _ => hL42 w hw A'' hR e he) hSend
    intro _ tree htree
    obtain ⟨hLtree, hLvh⟩ := proposal_viable_head_at S Sched x (viewFreeze S s₀) (s₀ + 1) w L _ _
      tree hDiv (hLw w hw) (by rw [Nat.add_sub_cancel]) (by omega) ⟨rfl, rfl⟩
      (hRootL w hw)
      (le_trans (floor_le_h_max _) (le_of_eq (hTall w hw).2.2.symm)) htree
    exact ⟨L, hLtree, hLvh, ancestorEq_refl L⟩
  -- the third clause: the confirmations of slot `s₀ + 1` (Lemma 79c)
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀ + 1 + 1) := by
    show anchorCW S tGAT ≤ slotStart S (s₀ + 2)
    omega
  have hMaj := committee_majority_of_committeeSleepiness S Sched (anchorCW S tGAT) (s₀ + 1)
    hCommittees hA2
  have hSub := (roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd (s₀ + 1) hMono hAwake
    (by omega) hEnd).1
  have hConf := lem79c_honestChainExtends_confirmations_step S Sched x GST s₀
    (Hon S Sched (s₀ + 1)) (S.P.committee (s₀ + 1) ∩ roundMembers S Sched (s₀ + 1 + 1)) L hDiv
    hMono hSync hCatch (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner
    (by omega) hVotes
    (fun w hwH t h1 h2 => hHonW w (hmem w hwH) t (by omega) h2)
    (fun u hu => by
      obtain ⟨hK, hR⟩ := Finset.mem_inter.1 hu
      obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ :=
        GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x (s₀ + 1) u hDiv
          hMono (hSub hR) hK
      exact ⟨hR, hK, vote, hvi, hvs, i, hl, hsent⟩)
    (fun v' _ => (counting_of_committee_majority S Sched x (s₀ + 1) (supportCutoff S (s₀ + 2))
      _ v' hMaj).2.1)
    (fun v' hv'H => finalized_compatible_fast_block S Sched x GST tAwakeEnd s₀ H₂
      (supportCutoff S (s₀ + 2)) v v' L C' A' hDiv hMono hSync hCatch
      (hRoots.mono (max_le le_rfl (supportCutoff_mono S (by omega)))) hU hThird hOld'
      (by omega) hEnd (fun t h1 h2 => hVW t (by omega) (by omega)) hv' hUpdate hSaved hLC' hLv' hL
      (by omega) le_rfl (hmem v' hv'H))
  refine ⟨hVotes, ?_, hConf⟩
  -- the second clause: the live locks after the revocation of slot `s₀ + 2`
  intro w hwH
  have hw := hmem w hwH
  exact locks_step_of_clauses S Sched x L s₀ w hDiv
    (fun A'' hR e he _ => hL42 w hw A'' hR e he)
    (fun Aw hUw Cw hCw => compatible_of_ancestorEq_both (ancestorEq_refl Cw) hLC'
      (lem31_saved_confirmations_compatible S Sched x GST s₀ w v Aw A' Cw C' hDiv hMono hSync
        hCatch (hRoots.mono (supportCutoff_mono S (by omega))) (by omega)
        (fun t h1 h2 => hHonW w hw t (by omega) (by omega))
        (fun t h1 h2 => hVW t (by omega) (by omega)) (hHonW w hw _ (by omega) (by omega)).2 hv'
        hUw hCw hUpdate hSaved))
    (fun t h1 h2 => hHonW w hw t (by have := dutyWindowStart_mono S (show s₀ + 1 ≤ s₀ + 2 by omega); omega) (by omega))

end GoldilocksCorrectness.Proofs.Executions
