module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityB6

@[expose] public section

/-!
# Lemma 89, part B: B5 and B6

B5 `window_last_confirmation_exists_of_no_change`, B6 `stability_fact3` and every lemma of their
kit that reads the fork-choice change `ForkChoiceChangeAt` (`Statements/Executions/Lemma89Defs.lean`,
the root disjunct counted only through `get_fc_root`'s first case, `h_max = h_j + 1`). The rest of
their kit is in `Lemma89Stability.lean` and `Lemma89StabilityB6.lean`.

First made as copies under the suffix `J`;
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

/-! ## Copied from `Lemma89Stability.lean` -/

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_mono
  dutyWindowStart_of_anchor dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono
  supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec compatible_symm'
  lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_contest_true_of floor_cases floor_le_h_max
  floor_of_root_ne_J h_max_le_floor_add_one h_max_sub_one_le_floor mem_viable_heads_iff root_cases)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)


/-- **A viable head stays a viable head while the validator's fork choice does not change.**
Under unforgeability, roots naming blocks, permanent corruption and fewer than a third of the
validators in the adversary set up to `tEnd`: when `u` is honest at `t₂ ≤ tEnd`, `t₁ ≤ t₂`, `u`
has no `ForkChoiceChangeAt` at any time from `t₁` to before `t₂`, and `W` is a viable head of
`u`'s frame before `t₁`, then `W` is a viable head of `u`'s frame before `t₂`.

Why: by induction on the time. At a step with no change, `head_height_floor` does not rise; the
root is given by `get_fc_root`'s first case (`h_max = h_j + 1`, not contested), and then it moves
to an ancestor of the old root, or by its second case, and then it is the finalized block, which is
an ancestor of `W`: `W`'s height is at least `head_height_floor`, which is greater than the cache
`h_j` in the second case, and `F_ancestorEq_of_high`. A finality move onto the justified block
falls in the second case.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t₁ ≤ t₂`: the times; `u`:
  the validator; `W`: the block.

Roots name blocks until `tR`, at least `tEnd`: the conclusion is for every time `t₂` at most
`tEnd`, and the step to `t + 1` reads `F_ancestorEq_of_high` at `t` and `t + 1`. -/
theorem viable_head_kept (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR) (tEnd t₁ : ℕ) (u : V) (W : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hW : W ∈ (fg_to_ac (stateBefore x t₁ u).S).viable_heads)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : tEnd ≤ tR) :
    ∀ t₂ : ℕ, t₁ ≤ t₂ → t₂ ≤ tEnd → u ∉ Sched.adv (t₂ : Int) →
      (∀ t : ℕ, t₁ ≤ t → t < t₂ → ¬ ForkChoiceChangeAt S Sched x u t) →
      W ∈ (fg_to_ac (stateBefore x t₂ u).S).viable_heads := by
  intro t₂ h12
  induction t₂, h12 using Nat.le_induction with
  | base => exact fun _ _ _ => hW
  | succ t h1t ih =>
    intro h2 hu hNo
    have hu' : u ∉ Sched.adv (t : Int) :=
      fun h => hu (hMono _ _ (by exact_mod_cast (Nat.le_succ t)) h)
    have hWt := ih (by omega) hu' (fun t' h1 h2 => hNo t' h1 (by omega))
    have hnc := hNo t h1t (Nat.lt_succ_self t)
    unfold ForkChoiceChangeAt at hnc
    push Not at hnc
    obtain ⟨hroot, hfl⟩ := hnc
    rw [mem_viable_heads_iff] at hWt ⊢
    obtain ⟨hWT, -, hrW, hflW⟩ := hWt
    have hWT' : W ∈ (stateBefore x (t + 1) u).S.T :=
      (stateBefore_grows x hDiv u (Nat.le_succ t)).1 hWT
    rw [σ_eq_of_stateBefore S Sched x t u W hWT] at hflW
    rw [σ_eq_of_stateBefore S Sched x (t + 1) u W hWT']
    have hfl' : head_height_floor (stateBefore x (t + 1) u).S ≤ (chainStateOf S.C W).h :=
      le_trans hfl hflW
    -- the new root is an ancestor of `W`
    have hroot' : (get_fc_root (stateBefore x (t + 1) u).S).AncestorEq W := by
      rcases root_cases (stateBefore x (t + 1) u).S with ⟨hJ, hm1, -⟩ | ⟨hF, hor⟩
      · exact ancestorEq_trans (hroot hJ hm1) (by rw [← fc_root_eq]; exact hrW)
      · have hm := h_j_lt_h_max S Sched x (t + 1) u
        have hfj : (stateBefore x (t + 1) u).S.h_j + 1 ≤
            head_height_floor (stateBefore x (t + 1) u).S := by
          rcases floor_cases (stateBefore x (t + 1) u).S with ⟨-, hme, hfl1⟩ | ⟨hcf, hfl1⟩
          · rw [hfl1, hme]
          · rcases hor with hc | hne
            · rw [hcf] at hc
              cases hc
            · rw [hfl1]
              unfold Height at *
              omega
        rw [hF]
        exact F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd (t + 1) t u u W hThird h2
          (by omega) hu hu' hWT (lt_of_lt_of_le (Nat.lt_of_succ_le hfj) hfl')
          (max_le (le_trans h2 htR) (by omega))
    exact ⟨hWT', ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ u) hroot',
      by rw [fc_root_eq]; exact hroot', hfl'⟩

/-- **With no fork-choice change, an honest vote of slot `σ` extends the finalized block of a
validator honest at a time `b` at or after the vote time of slot `σ`.** Under the execution assumptions and
unforgeability, from `GST` on, with fewer than a third of the validators in the adversary set up to
`tEnd`; write `a₀` for the time `2Δ` into slot `σ − 1`, one delay before the view freeze of slot
`σ − 1`: when `v` is honest at `b ≤ tEnd`, `b` at least the vote time of slot `σ`, `u` is awake and
honest from `a₀` to the vote time of slot `σ`, `v` has no `ForkChoiceChangeAt` from `a₀` to before
`b`, `u` has none from the view freeze of slot `σ − 1` to before the vote time of slot `σ`, and
`u`'s tick at that vote time put `vote` on the wire — then `vote` is `u`'s slot-`σ` vote for a block
`H_u` it holds, and `v`'s finalized block before `b` is `H_u` or an ancestor of `H_u`.

Why (`F'` is `v`'s finalized block, `f` the finalization height of the chain state that finalized
it, `h_j` is `u`'s cache at the vote time): when `u`'s root is its justified block `J_u`, at a
height `h_j`: if `h_j > f`, Lemma 89a puts `F'` on `J_u`'s chain; if `h_j = f`, Lemma 76 makes
`J_u = F'`; and the vote extends the root. When `u`'s root is its finalized block,
`head_height_floor` is greater than `h_j`, and if `h_j ≥ f` every viable head is higher than `f`,
so on `F'`'s chain (Lemma 89a), while no strict ancestor of `F'` is viable: the vote extends `F'`
(`honest_vote_spec`, with a viable head held before the view freeze and kept to the vote time,
`viable_head_kept`). It remains `h_j < f ≤ v`'s cache `h_j` at `b`. If `v`'s cache was at least `f`
at `a₀`, the block witnessing it reaches `u` by the view freeze, against `h_j < f`. Otherwise `v`'s
cache passes `f` at some time `t` from `a₀` to `b`: then `v`'s root moves to its new justified
block, or its `head_height_floor` rises, unless `v`'s `h_max` is then at least `f + 2`; if that was
already so at `a₀`, a block of that height reaches `u` and `u`'s `head_height_floor` is greater than
`f` (the case before); otherwise `v`'s `h_max` reached `f + 2` while its cache was less than `f`,
and its `head_height_floor` rose then. Each change is against the hypothesis.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `b`: the times; `σ`: the
  slot of the vote; `u`: the voter; `v`: the validator whose finalized block is read; `vote`: the
  vote.

Roots name blocks until `b`: the proof reads `v`'s blocks before `b`, `u`'s before the vote time
of slot `σ`, at most `b`, and blocks held by `v` at times from `a₀` to `b`. -/
theorem vote_extends_finalized_at_of_no_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd σ b : ℕ) (u v : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hσ : 1 ≤ σ) (hGST : GST ≤ slotStart S (σ - 1) + 2 * Δ S)
    (hEnd : b ≤ tEnd) (hab : voteTime S σ ≤ b)
    (hv : v ∉ Sched.adv (b : Int))
    (hu : ∀ t : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t → t ≤ voteTime S σ →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int))
    (hNoV : ∀ t : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t → t < b →
      ¬ ForkChoiceChangeAt S Sched x v t)
    (hNoU : ∀ t : ℕ, viewFreeze S (σ - 1) ≤ t → t < voteTime S σ →
      ¬ ForkChoiceChangeAt S Sched x u t)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
      vote = GoldfishVote.mk u σ H_u.root ∧
      (stateBefore x (b) v).S.F.AncestorEq H_u := by
  -- the times: `a₀`, the view freeze `a₀ + Δ`, the vote time and the cutoff `b`
  have hΔ := one_le_Δ S
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ
  have hss : slotStart S σ = slotStart S (σ - 1) + 4 * Δ S := by
    rw [← hσ', slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one, hσ']
  have hss' : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hfz : viewFreeze S (σ - 1) = slotStart S (σ - 1) + 3 * Δ S := viewFreeze_eq S (σ - 1)
  have hvt : voteTime S σ = slotStart S σ + Δ S := voteTime_eq S σ
  have hvt' : voteTime S (σ + 1) = slotStart S (σ + 1) + Δ S := voteTime_eq S (σ + 1)
  have hfzΔ : slotStart S (σ - 1) + 2 * Δ S + Δ S = viewFreeze S (σ - 1) := by omega
  have hvhon : ∀ t : ℕ, t ≤ b → v ∉ Sched.adv (t : Int) :=
    fun t ht h => hv (hMono _ _ (by exact_mod_cast ht) h)
  have huvt : u ∉ Sched.adv (voteTime S σ : Int) := (hu (voteTime S σ) (by omega) le_rfl).2
  -- the vote
  obtain ⟨H_u, hHT, hvote, hρH, hG⟩ := honest_vote_spec S Sched x hDiv σ u vote hSend
  refine ⟨H_u, hHT, hvote, ?_⟩
  -- `v`'s finalized block `F'`, finalized by the chain state of `D` at the height `f`
  obtain ⟨D, hD, hF⟩ := finalizedFromChain_of_exec S Sched x
    (stepBefore x (b)) v
  have hSt : stateBefore x (b) v =
      x[stepBefore x (b)][v].st := rfl
  rw [← hSt] at hD hF
  by_cases hgen : (stateBefore x (b) v).S.F = Block.genesis
  · rw [hgen]
    exact genesis_ancestorEq H_u
  have hf1 : 1 ≤ (chainStateOf S.C D).h_F := by
    by_contra h0
    apply hgen
    rw [hF]
    exact GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D
      (Nat.lt_one_iff.mp (Nat.lt_of_not_le h0))
  obtain ⟨hcertF, -, hFD, hFh⟩ :=
    (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2 hf1
  rw [← hF] at hcertF hFD hFh
  have hFT : (stateBefore x (b) v).S.F ∈
      (stateBefore x (b) v).S.T :=
    ancestors_mem_T_of_exec S Sched x _ v D _ hD hFD
  have hjD : ((stateBefore x (b) v).S.σ D).h_j ≤
      (stateBefore x (b) v).S.h_j :=
    h_j_of_mem_T_of_stateBefore S Sched x _ v D hD hFD
  rw [σ_eq_of_stateBefore S Sched x _ v D hD] at hjD
  have hFjD := (lem47_chain_state_heights S.C D D).1.2.2
  -- `G`: when `u`'s `head_height_floor` is greater than `f`, the vote extends `F'`
  have G : (chainStateOf S.C D).h_F <
      head_height_floor (stateBefore x (voteTime S σ) u).S →
      (stateBefore x (b) v).S.F.AncestorEq H_u := by
    intro hflf
    obtain ⟨W₀, hW₀⟩ := frame_has_viable_head S Sched x (viewFreeze S (σ - 1)) u
    have hW₀T : W₀ ∈ (stateBefore x (viewFreeze S (σ - 1)) u).S.T :=
      ((mem_viable_heads_iff _ _).1 hW₀).1
    have hW₀v := viable_head_kept S Sched x hDiv hMono hU hRoots b (viewFreeze S (σ - 1)) u W₀
      (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird) hW₀ le_rfl (voteTime S σ)
      (by omega) (by omega) huvt hNoU
    refine hG (viewFreeze S (σ - 1)) W₀ _ hW₀T le_rfl (by omega) hW₀v ?_ ?_
    · intro W hW
      obtain ⟨hWT, -, -, hWfl⟩ := (mem_viable_heads_iff _ _).1 hW
      rw [σ_eq_of_stateBefore S Sched x _ u W hWT] at hWfl
      rw [hF]
      exact finalized_ancestorEq_of_held S Sched x hMono hU hRoots tEnd _ _ v u D W hThird hEnd
        (by omega) hv huvt hD hWT (lt_of_lt_of_le hflf hWfl) (max_le (by omega) (by omega))
    · intro B hBF hne hBv
      obtain ⟨hBT, -, -, hBfl⟩ := (mem_viable_heads_iff _ _).1 hBv
      rw [σ_eq_of_stateBefore S Sched x _ u B hBT] at hBfl
      have hBh := (lem47_chain_state_heights S.C B
        (stateBefore x (b) v).S.F).2.2.2.1 hBF
      rw [hFh] at hBh
      exact absurd (lt_of_lt_of_le hflf (le_trans hBfl hBh)) (lt_irrefl _)
  -- the delivery from `v` at `a₀` to `u` by the view freeze, of a block higher than `f`
  have hjufz : (stateBefore x (viewFreeze S (σ - 1)) u).S.h_j ≤
      (stateBefore x (voteTime S σ) u).S.h_j :=
    h_j_mono S Sched x hDiv hMono hU hRoots tEnd _ _ u hThird (by omega) (by omega) huvt (by omega)
  -- `X`: the case where `u`'s cache `h_j` is less than `f`
  have X : (stateBefore x (voteTime S σ) u).S.h_j < (chainStateOf S.C D).h_F →
      (stateBefore x (b) v).S.F.AncestorEq H_u := by
    intro hju
    have hdeliver : ∀ Y : Block V, Y ∈ (stateBefore x (slotStart S (σ - 1) + 2 * Δ S) v).S.T →
        (chainStateOf S.C D).h_F < (chainStateOf S.C Y).h →
        Y ∈ (stateBefore x (voteTime S σ) u).S.T := by
      intro Y hY hYh
      have h1 := mem_T_of_delivery_high S Sched x GST hDiv hMono hSync hCatch hRoots
        hParent hU tEnd (slotStart S (σ - 1) + 2 * Δ S) v u Y hThird (by omega) (by omega) hGST
        (hvhon _ (by omega)) hY (fun t' h1 h2 => hu t' h1 (by omega))
        (by rw [hfzΔ]; exact lt_of_le_of_lt hjufz (lt_trans hju hYh)) (by omega)
      rw [hfzΔ] at h1
      exact (stateBefore_grows x hDiv u (show viewFreeze S (σ - 1) ≤ voteTime S σ by omega)).1 h1
    by_cases hX1 : (chainStateOf S.C D).h_F ≤
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S) v).S.h_j
    · -- `v`'s cache was at least `f` at `a₀`: its witness reaches `u`
      exfalso
      obtain ⟨⟨Wv, hWv, -, hjWv⟩, -, -⟩ :=
        cachesWitnessed_of_stateBefore S Sched x (slotStart S (σ - 1) + 2 * Δ S) v
      have hWvh := (lem47_chain_state_heights S.C Wv Wv).1.2.1
      rw [hjWv] at hX1
      have hWvu := hdeliver Wv hWv (lt_of_le_of_lt hX1 hWvh)
      have hFW := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd _ _ u u Wv hThird
        (by omega) (by omega) huvt huvt hWvu (lt_trans (lt_of_lt_of_le hju hX1) hWvh)
        (max_le (by omega) (by omega))
      have hjW := h_j_of_mem_T_of_stateBefore S Sched x _ u Wv hWvu hFW
      rw [σ_eq_of_stateBefore S Sched x _ u Wv hWvu] at hjW
      exact absurd (lt_of_lt_of_le hju (le_trans hX1 hjW)) (lt_irrefl _)
    push Not at hX1
    -- the first time `v`'s cache reaches `f`
    have hexP : ∃ n : ℕ, (chainStateOf S.C D).h_F ≤
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + n) v).S.h_j := by
      refine ⟨b - (slotStart S (σ - 1) + 2 * Δ S), ?_⟩
      rw [show slotStart S (σ - 1) + 2 * Δ S +
          (b - (slotStart S (σ - 1) + 2 * Δ S)) =
          b by omega]
      exact le_trans hFjD hjD
    classical
    have hn₀ := Nat.find_spec hexP
    have hmin : ∀ m < Nat.find hexP, ¬ (chainStateOf S.C D).h_F ≤
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.h_j :=
      fun m hm => Nat.find_min hexP hm
    have hn₀b : Nat.find hexP ≤ b - (slotStart S (σ - 1) + 2 * Δ S) := by
      by_contra h
      apply hmin _ (Nat.lt_of_not_le h)
      rw [show slotStart S (σ - 1) + 2 * Δ S +
          (b - (slotStart S (σ - 1) + 2 * Δ S)) =
          b by omega]
      exact le_trans hFjD hjD
    have hn₀0 : Nat.find hexP ≠ 0 := by
      intro h0
      rw [h0, Nat.add_zero] at hn₀
      exact absurd (lt_of_lt_of_le hX1 hn₀) (lt_irrefl _)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn₀0
    rw [hm] at hn₀ hn₀b
    rw [Nat.succ_eq_add_one, ← Nat.add_assoc] at hn₀
    have hj0 : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.h_j <
        (chainStateOf S.C D).h_F := Nat.lt_of_not_le (hmin m (by omega))
    have hnc := hNoV (slotStart S (σ - 1) + 2 * Δ S + m) (by omega) (by omega)
    have hvm1 : v ∉ Sched.adv ((slotStart S (σ - 1) + 2 * Δ S + m + 1 : ℕ) : Int) :=
      hvhon _ (by omega)
    have hm1 := h_j_lt_h_max S Sched x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v
    have hm0 := h_j_lt_h_max S Sched x (slotStart S (σ - 1) + 2 * Δ S + m) v
    have hmm := h_max_mono S Sched x hDiv v
      (Nat.le_succ (slotStart S (σ - 1) + 2 * Δ S + m))
    have hfl0le := floor_le_h_max (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S
    rcases floor_cases (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S with
      ⟨hc1, hme1, hfl1⟩ | ⟨hc1, hfl1⟩
    · -- contested after: `head_height_floor` rises
      exfalso
      apply hnc
      right
      rw [hfl1]
      rcases floor_cases (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S with
        ⟨-, hme0, hfl0⟩ | ⟨-, hfl0⟩
      · rw [hfl0, hme0, hme1]
        exact Nat.succ_lt_succ (lt_of_lt_of_le hj0 hn₀)
      · rw [hfl0]
        exact lt_of_lt_of_le (Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) hm0) Nat.one_pos) hmm
    by_cases hme1 : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.h_max =
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.h_j + 1
    · -- the root moves to the new justified block
      exfalso
      apply hnc
      left
      have hr1 : get_fc_root (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S =
          (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.J := by
        rcases root_cases (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S with
          ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · rcases h with h | h
          · rw [hc1] at h
            cases h
          · exact absurd hme1 h
      refine ⟨hr1, hme1, ?_⟩
      intro hJr
      rw [hr1] at hJr
      have hr0J : (get_fc_root (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S).AncestorEq
          (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.J := by
        rcases root_cases (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S with
          ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]
          exact ancestorEq_refl _
        · rw [h]
          exact F_ancestorEq_J_of_stateBefore S Sched x _ v
      have hJJ := ancestorEq_trans hJr hr0J
      obtain ⟨⟨W₁, hW₁, hJW₁, hjW₁⟩, -, -⟩ :=
        cachesWitnessed_of_stateBefore S Sched x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v
      obtain ⟨⟨W₀, -, hJW₀, hjW₀⟩, -, -⟩ :=
        cachesWitnessed_of_stateBefore S Sched x (slotStart S (σ - 1) + 2 * Δ S + m) v
      have h1j : 1 ≤ (chainStateOf S.C W₁).h_j := by
        rw [← hjW₁]
        exact le_trans hf1 hn₀
      have hJ1h : (chainStateOf S.C
          (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.J).h =
          (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.h_j := by
        rw [hJW₁, hjW₁]
        exact (chainStateOf_J_spec S.C W₁).2.2 h1j
      by_cases h00 : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.h_j = 0
      · -- the earlier justified block is the genesis block
        have hJ0 : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.J = Block.genesis := by
          rw [hJW₀]
          exact (chainStateOf_J_spec S.C W₀).2.1 (by rw [← hjW₀]; exact h00)
        rw [hJ0] at hJJ
        have hJ1g := (GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff _).1 hJJ
        have hgF := (lem47_chain_state_heights S.C Block.genesis
          (stateBefore x (b) v).S.F).2.2.2.1 (genesis_ancestorEq _)
        rw [hFh] at hgF
        rw [hJ1g] at hJ1h
        have heq : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.h_j =
            (chainStateOf S.C D).h_F := le_antisymm (hJ1h ▸ hgF) hn₀
        obtain ⟨hcert1, -, -⟩ :=
          (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C W₁).1 h1j
        rw [← hJW₁, ← hjW₁, heq, hJ1g] at hcert1
        have hge := eq_of_cert_same_height S Sched x hMono hU hRoots tEnd
          (slotStart S (σ - 1) + 2 * Δ S + m + 1) (b) v v W₁ D
          Block.genesis _ _ hThird (by omega) hEnd hvm1 hv hW₁ hD hcert1 hcertF
          (genesis_mem_T_of_exec S Sched x _ v) hFT (max_le (by omega) (by omega))
        exact hgen hge.symm
      · have hJ0h : (chainStateOf S.C
            (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.J).h =
            (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m) v).S.h_j := by
          rw [hJW₀, hjW₀]
          exact (chainStateOf_J_spec S.C W₀).2.2
            (by rw [← hjW₀]; exact Nat.one_le_iff_ne_zero.mpr h00)
        have hmono := (lem47_chain_state_heights S.C _ _).2.2.2.1 hJJ
        rw [hJ1h, hJ0h] at hmono
        exact absurd (lt_of_le_of_lt hmono (lt_of_lt_of_le hj0 hn₀)) (lt_irrefl _)
    -- `v`'s `h_max` after is at least `f + 2`
    have hm2 : (chainStateOf S.C D).h_F + 2 ≤
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + m + 1) v).S.h_max := by
      unfold Height at *
      omega
    by_cases hci : (chainStateOf S.C D).h_F + 2 ≤
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S) v).S.h_max
    · -- already at `a₀`: a block of that height reaches `u`
      obtain ⟨-, ⟨Xb, hXb, hXbh⟩, -⟩ :=
        cachesWitnessed_of_stateBefore S Sched x (slotStart S (σ - 1) + 2 * Δ S) v
      have hXu := hdeliver Xb hXb (by rw [hXbh]; unfold Height at *; omega)
      have hhm := height_le_h_max S Sched x _ u Xb hXu
      have hfu := h_max_sub_one_le_floor (stateBefore x (voteTime S σ) u).S
      apply G
      rw [hXbh] at hhm
      unfold Height at *
      omega
    · -- `v`'s `h_max` reached `f + 2` while its cache was less than `f`
      exfalso
      push Not at hci
      have hexQ : ∃ n : ℕ, (chainStateOf S.C D).h_F + 2 ≤
          (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + n) v).S.h_max :=
        ⟨m + 1, by rw [← Nat.add_assoc]; exact hm2⟩
      have hn₁ := Nat.find_spec hexQ
      have hmin₁ : ∀ k < Nat.find hexQ, ¬ (chainStateOf S.C D).h_F + 2 ≤
          (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + k) v).S.h_max :=
        fun k hk => Nat.find_min hexQ hk
      have hn₁m : Nat.find hexQ ≤ m + 1 := Nat.find_min' hexQ (by rw [← Nat.add_assoc]; exact hm2)
      have hn₁0 : Nat.find hexQ ≠ 0 := by
        intro h0
        rw [h0, Nat.add_zero] at hn₁
        exact absurd (lt_of_lt_of_le hci hn₁) (lt_irrefl _)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn₁0
      rw [hk] at hn₁ hn₁m
      rw [Nat.succ_eq_add_one, ← Nat.add_assoc] at hn₁
      have hk0 : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + k) v).S.h_max <
          (chainStateOf S.C D).h_F + 2 := Nat.lt_of_not_le (hmin₁ k (by omega))
      have hjk : (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + k) v).S.h_j <
          (chainStateOf S.C D).h_F := by
        by_cases hkm : k = m
        · rw [hkm]
          exact hj0
        · exact Nat.lt_of_not_le (hmin k (by omega))
      apply hNoV (slotStart S (σ - 1) + 2 * Δ S + k) (by omega) (by omega)
      right
      have hfk1 := h_max_sub_one_le_floor
        (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + k + 1) v).S
      rcases floor_cases (stateBefore x (slotStart S (σ - 1) + 2 * Δ S + k) v).S with
        ⟨-, hmek, hflk⟩ | ⟨-, hflk⟩
      · rw [hflk]
        unfold Height at *
        omega
      · rw [hflk]
        unfold Height at *
        omega
  -- the cases on `u`'s root
  rcases root_cases (stateBefore x (voteTime S σ) u).S with ⟨hrJ, -, -⟩ | ⟨-, hcF⟩
  · obtain ⟨⟨Wu, hWu, hJWu, hjWu⟩, -, -⟩ :=
      cachesWitnessed_of_stateBefore S Sched x (voteTime S σ) u
    have hJT : (stateBefore x (voteTime S σ) u).S.J ∈ (stateBefore x (voteTime S σ) u).S.T :=
      (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S σ)) u).2.2.1
    have hρJ : (stateBefore x (voteTime S σ) u).S.J.AncestorEq H_u := hrJ ▸ hρH
    rcases lt_trichotomy (chainStateOf S.C D).h_F (stateBefore x (voteTime S σ) u).S.h_j with
      hlt | heq | hgt
    · -- `u`'s justified block is higher than `f`: Lemma 89a
      have h1j : 1 ≤ (chainStateOf S.C Wu).h_j := by
        rw [← hjWu]
        exact le_trans hf1 hlt.le
      have hJh : (chainStateOf S.C (stateBefore x (voteTime S σ) u).S.J).h =
          (stateBefore x (voteTime S σ) u).S.h_j := by
        rw [hJWu, hjWu]
        exact (chainStateOf_J_spec S.C Wu).2.2 h1j
      have hFJ := finalized_ancestorEq_of_held S Sched x hMono hU hRoots tEnd _ _ v u D _ hThird
        hEnd (by omega) hv huvt hD hJT (by rw [hJh]; exact hlt) (max_le (by omega) (by omega))
      rw [hF]
      exact ancestorEq_trans hFJ hρJ
    · -- at the same height: Lemma 76
      have h1j : 1 ≤ (chainStateOf S.C Wu).h_j := by
        rw [← hjWu, ← heq]
        exact hf1
      obtain ⟨hcertJ, -, -⟩ :=
        (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C Wu).1 h1j
      rw [← hJWu, ← hjWu, ← heq] at hcertJ
      have heqJ := eq_of_cert_same_height S Sched x hMono hU hRoots tEnd _ _ v u D Wu _ _ _
        hThird hEnd (by omega) hv huvt hD hWu hcertF hcertJ hFT hJT (max_le (by omega) (by omega))
      rw [heqJ]
      exact hρJ
    · exact X hgt
  · have hfl : (stateBefore x (voteTime S σ) u).S.h_j + 1 ≤
        head_height_floor (stateBefore x (voteTime S σ) u).S := by
      have hm := h_j_lt_h_max S Sched x (voteTime S σ) u
      rcases floor_cases (stateBefore x (voteTime S σ) u).S with ⟨-, hme, hfl⟩ | ⟨hc, hfl⟩
      · rw [hfl, hme]
      · rcases hcF with h | h
        · rw [hc] at h
          cases h
        · rw [hfl]
          unfold Height at *
          omega
    by_cases hle : (chainStateOf S.C D).h_F ≤ (stateBefore x (voteTime S σ) u).S.h_j
    · exact G (lt_of_le_of_lt hle (Nat.lt_of_succ_le hfl))
    · exact X (Nat.lt_of_not_le hle)

/-- **With no fork-choice change, an honest vote of slot `σ` extends the finalized block of a
validator honest at the update of slot `σ`.** Under the execution assumptions and
unforgeability, from `GST` on, with fewer than a third of the validators in the adversary set up to
`tEnd`; write `a₀` for the time `2Δ` into slot `σ − 1`, one delay before the view freeze of slot
`σ − 1`: when `v` is honest at the support cutoff `b` of slot `σ + 1 ≤ tEnd`, `u` is awake and
honest from `a₀` to the vote time of slot `σ`, `v` has no `ForkChoiceChangeAt` from `a₀` to before
`b`, `u` has none from the view freeze of slot `σ − 1` to before the vote time of slot `σ`, and
`u`'s tick at that vote time put `vote` on the wire — then `vote` is `u`'s slot-`σ` vote for a block
`H_u` it holds, and `v`'s finalized block before `b` is `H_u` or an ancestor of `H_u`.

The instance `b := supportCutoff S (σ + 1)` of
`vote_extends_finalized_at_of_no_change`.

Why (`F'` is `v`'s finalized block, `f` the finalization height of the chain state that finalized
it, `h_j` is `u`'s cache at the vote time): when `u`'s root is its justified block `J_u`, at a
height `h_j`: if `h_j > f`, Lemma 89a puts `F'` on `J_u`'s chain; if `h_j = f`, Lemma 76 makes
`J_u = F'`; and the vote extends the root. When `u`'s root is its finalized block,
`head_height_floor` is greater than `h_j`, and if `h_j ≥ f` every viable head is higher than `f`,
so on `F'`'s chain (Lemma 89a), while no strict ancestor of `F'` is viable: the vote extends `F'`
(`honest_vote_spec`, with a viable head held before the view freeze and kept to the vote time,
`viable_head_kept`). It remains `h_j < f ≤ v`'s cache `h_j` at `b`. If `v`'s cache was at least `f`
at `a₀`, the block witnessing it reaches `u` by the view freeze, against `h_j < f`. Otherwise `v`'s
cache passes `f` at some time `t` from `a₀` to `b`: then `v`'s root moves to its new justified
block, or its `head_height_floor` rises, unless `v`'s `h_max` is then at least `f + 2`; if that was
already so at `a₀`, a block of that height reaches `u` and `u`'s `head_height_floor` is greater than
`f` (the case before); otherwise `v`'s `h_max` reached `f + 2` while its cache was less than `f`,
and its `head_height_floor` rose then. Each change is against the hypothesis.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`: the times; `σ`: the
  slot of the vote; `u`: the voter; `v`: the validator whose finalized block is read; `vote`: the
  vote.

Roots name blocks until `supportCutoff S (σ + 1)`: `vote_extends_finalized_at_of_no_change` at
`b := supportCutoff S (σ + 1)`. -/
theorem vote_extends_finalized_of_no_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd σ : ℕ) (u v : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (σ + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hσ : 1 ≤ σ) (hGST : GST ≤ slotStart S (σ - 1) + 2 * Δ S)
    (hEnd : supportCutoff S (σ + 1) ≤ tEnd)
    (hv : v ∉ Sched.adv (supportCutoff S (σ + 1) : Int))
    (hu : ∀ t : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t → t ≤ voteTime S σ →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int))
    (hNoV : ∀ t : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t → t < supportCutoff S (σ + 1) →
      ¬ ForkChoiceChangeAt S Sched x v t)
    (hNoU : ∀ t : ℕ, viewFreeze S (σ - 1) ≤ t → t < voteTime S σ →
      ¬ ForkChoiceChangeAt S Sched x u t)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
      vote = GoldfishVote.mk u σ H_u.root ∧
      (stateBefore x (supportCutoff S (σ + 1)) v).S.F.AncestorEq H_u :=
  vote_extends_finalized_at_of_no_change S Sched x GST tEnd σ (supportCutoff S (σ + 1)) u v vote
    hDiv hMono hSync hCatch hRoots hParent hU hThird hσ hGST hEnd
    (le_trans (by rw [supportCutoff_eq]; exact Nat.le_add_right _ _)
      (supportCutoff_mono S (Nat.le_succ σ))) hv hu hNoV hNoU hSend

/-- **B5 with no fork-choice change: the window's last slot has a confirmation.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route (`σ := s − 2`): committee sleepiness at slot `σ + 1` gives the honest members `Hs` of the
committee of slot `σ`, more than half of it, all honest active at slot `σ`; take an updater `v` in
`Hs`. Every honest vote of slot `σ` extends `v`'s finalized block before the support cutoff of slot
`σ + 1` (`vote_extends_finalized_of_no_change`, the times it reads being inside the window), so
the update saves a confirmation (`confirmation_saved_of_votes`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  phase; `r`: the round; `s`: the honest round opening slot.

Roots name blocks until `supportCutoff S (s - 1)`: `vote_extends_finalized_of_no_change` at slot
`s − 2`, and `confirmation_saved_of_votes` at slot `s − 2`. -/
theorem window_last_confirmation_exists_of_no_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r s : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hk : S.C.k + 1 ≤ s)
    (hBefore : supportCutoff S s ≤ aR S r)
    (hAnchor : anchorCW S tGAT ≤ slotStart S (s - S.C.k))
    (hNoChange : ∀ (w : V) (t' : ℕ), voteTime S (s - S.C.k - 1) ≤ t' → t' < voteTime S s →
      w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') :
    ∃ v ∈ Hon S Sched (s - 2), ∃ D : Block V,
      (stateBefore x (supportCutoff S (s - 1) + 1) v).A.saved_confirmation (s - 2) = some D := by
  have hk2 := S.C.k_ge_two
  have hΔ := one_le_Δ S
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 2 := ⟨s - 2, by omega⟩
  rw [show σ + 2 - 2 = σ by omega, show σ + 2 - 1 = σ + 1 by omega]
  have hσ : 1 ≤ σ := by omega
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ
  -- the times
  have hw₀ : σ + 2 - S.C.k - 1 ≤ σ - 1 := by omega
  have hsw := slotStart_mono S hw₀
  have hss : slotStart S σ = slotStart S (σ - 1) + 4 * Δ S := by
    rw [← hσ', slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one, hσ']
  have hss' : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss'' : slotStart S (σ + 2) = slotStart S (σ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (σ + 1)]
    exact Nat.mul_succ _ _
  have hvw := voteTime_eq S (σ + 2 - S.C.k - 1)
  have hvσ := voteTime_eq S σ
  have hvσ2 := voteTime_eq S (σ + 2)
  have hvσ1 := voteTime_eq S (σ + 1)
  have hb := supportCutoff_eq S (σ + 1)
  have hfz : viewFreeze S (σ - 1) = slotStart S (σ - 1) + 3 * Δ S := viewFreeze_eq S (σ - 1)
  have hbEnd : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ (σ + 1))) (le_trans hBefore hEnd)
  -- the committee of slot `σ` and its honest members
  have hanc : anchorCW S tGAT ≤ slotStart S (σ + 1) :=
    le_trans hAnchor (slotStart_mono S (by omega))
  have hMaj := committee_majority_of_committeeSleepiness S Sched (anchorCW S tGAT) σ hCommittees
    hanc
  have hdw := dutyWindowStart_of_anchor S tGAT σ hanc
  have hdwσ : dutyWindowStart S σ ≤ slotStart S (σ - 1) := by
    have h := dutyWindowStart_succ_le_slotStart S (σ - 1)
    rw [hσ'] at h
    exact h
  have hsub := (roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd σ hMono hAwake
    (by omega) hbEnd).1
  obtain ⟨v, hvHs⟩ : (S.P.committee σ ∩ roundMembers S Sched (σ + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hvR : v ∈ roundMembers S Sched (σ + 1) := (Finset.mem_inter.1 hvHs).2
  have hvb : v ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hvR).2
  have hvA := honestActiveAt_window S Sched σ v hMono (hsub hvR)
  -- every honest vote of slot `σ` extends `v`'s finalized block
  have hC1 : ∀ u ∈ S.P.committee σ ∩ roundMembers S Sched (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
        vote = GoldfishVote.mk u σ H_u.root ∧
        (stateBefore x (supportCutoff S (σ + 1)) v).S.F.AncestorEq H_u := by
    intro u hu vote hSend
    have huA := honestActiveAt_window S Sched σ u hMono (hsub (Finset.mem_inter.1 hu).2)
    exact vote_extends_finalized_of_no_change S Sched x GST tAwakeEnd σ u v vote hDiv hMono hSync
      hCatch (hRoots.mono (supportCutoff_mono S (by omega))) hParent hU hThird hσ (by omega)
      hbEnd hvb
      (fun t h1 h2 => huA t (by omega) (by omega))
      (fun t h1 h2 => hNoChange v t (by omega) (by omega)
        (fun h => hvb (hMono _ _ (by exact_mod_cast (show t ≤ supportCutoff S (σ + 1) by omega))
          h)))
      (fun t h1 h2 => hNoChange u t (by omega) (by omega) (huA t (by omega) (by omega)).2)
      hSend
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) _ hDiv hMono
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩) hC1
  obtain ⟨D, hD⟩ := confirmation_saved_of_votes S Sched x GST σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) H v hDiv hMono hSync hCatch
    (hRoots.mono (supportCutoff_mono S (by omega)))
    hParent hOwner (by omega)
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2, (hH u hu).1, (hH u hu).2.1,
      (hH u hu).2.2⟩)
    (counting_of_committee_majority S Sched x σ (supportCutoff S (σ + 1))
      (roundMembers S Sched (σ + 1)) v hMaj).2.1
    (fun t h1 h2 => hvA t (le_trans (dutyWindowStart_mono S (Nat.le_succ σ)) h1) h2)
  exact ⟨v, hvR, D, hD⟩

end GoldilocksCorrectness.Proofs.Executions

/-! ## Copied from `Lemma89StabilityB6.lean` -/

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)


/-- **With no fork-choice change, `head_height_floor` does not rise.** When `p` has no
`ForkChoiceChangeAt` at any time from `t₁` to before `t₂`, its `head_height_floor` before `t₂` is
at most the one before `t₁`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `p`: the validator; `t₁ ≤ t₂`: the
  times. -/
theorem floor_le_of_no_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (p : V) (t₁ : ℕ) :
    ∀ t₂ : ℕ, t₁ ≤ t₂ → (∀ t : ℕ, t₁ ≤ t → t < t₂ → ¬ ForkChoiceChangeAt S Sched x p t) →
      head_height_floor (stateBefore x t₂ p).S ≤ head_height_floor (stateBefore x t₁ p).S := by
  intro t₂ h12
  induction t₂, h12 using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ t h1t ih =>
    intro hNo
    have h := ih (fun t' h1 h2 => hNo t' h1 (by omega))
    have hnc := hNo t h1t (Nat.lt_succ_self t)
    unfold ForkChoiceChangeAt at hnc
    push Not at hnc
    exact le_trans hnc.2 h

/-- **With no fork-choice change, `h_max` stays at most one more than `head_height_floor` (the least chain-state height a viable block may have) at the start.**

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `p`: the validator; `t₁ ≤ t₂`: the
  times. -/
theorem h_max_le_of_no_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (p : V) (t₁ t₂ : ℕ) (h12 : t₁ ≤ t₂)
    (hNo : ∀ t : ℕ, t₁ ≤ t → t < t₂ → ¬ ForkChoiceChangeAt S Sched x p t) :
    (stateBefore x t₂ p).S.h_max ≤ head_height_floor (stateBefore x t₁ p).S + 1 :=
  le_trans (h_max_le_floor_add_one _) (Nat.succ_le_succ (floor_le_of_no_change S Sched x p t₁ t₂
    h12 hNo))

/-- **With no fork-choice change, the cache `h_j` does not pass a height `j` while `h_max` stays at
most `j + 1`, unless the justified block is the genesis block.** Under unforgeability, roots naming
blocks, permanent corruption and fewer than a third of the validators in the adversary set up to
`tEnd`: when `p` is honest at `t₂ ≤ tEnd`, has no `ForkChoiceChangeAt` from `t₁` to before `t₂`,
its cache `h_j` is less than `j` before `t₁` and at least `j` before `t₂`, and its `h_max` before
`t₂` is at most `j + 1`, then its justified block before `t₂` is the genesis block.

Why: at the first time the cache reaches `j`, it is `j` and `h_max` is `j + 1`; a contested state
then has `head_height_floor = j + 1`, more than before (a rise); otherwise the root is the new
justified block, at the height `j`, and with no change it is an ancestor of the old root, so of
the old justified block, at a height less than `j` unless that block is the genesis block; then
the new one is too, and Lemma 76 carries it to `t₂`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t₁ ≤ t₂`: the times;
  `j`: the height; `p`: the validator.

Roots name blocks until `tR`, at least `t₂`: the proof compares two justified blocks of `p` read
before `t₂` at the latest (`J_eq_of_h_j_eq`). -/
theorem J_genesis_of_cache_passes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR) (tEnd t₁ t₂ j : ℕ) (p : V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (h12 : t₁ ≤ t₂) (ht₂ : t₂ ≤ tEnd)
    (hp : p ∉ Sched.adv (t₂ : Int))
    (hNo : ∀ t : ℕ, t₁ ≤ t → t < t₂ → ¬ ForkChoiceChangeAt S Sched x p t)
    (hlt : (stateBefore x t₁ p).S.h_j < j) (hge : j ≤ (stateBefore x t₂ p).S.h_j)
    (hm : (stateBefore x t₂ p).S.h_max ≤ j + 1)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t₂ ≤ tR) :
    (stateBefore x t₂ p).S.J = Block.genesis := by
  unfold Height at *
  have hex : ∃ n : ℕ, j ≤ (stateBefore x (t₁ + n) p).S.h_j :=
    ⟨t₂ - t₁, by rw [show t₁ + (t₂ - t₁) = t₂ by omega]; exact hge⟩
  classical
  have hn₀ := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ j ≤ (stateBefore x (t₁ + m) p).S.h_j :=
    fun m hm => Nat.find_min hex hm
  have hn₀b : Nat.find hex ≤ t₂ - t₁ :=
    Nat.find_min' hex (by rw [show t₁ + (t₂ - t₁) = t₂ by omega]; exact hge)
  have hn₀0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hn₀
    omega
  obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hn₀0
  rw [hm'] at hn₀ hn₀b
  rw [Nat.succ_eq_add_one, ← Nat.add_assoc] at hn₀
  have hj0 : (stateBefore x (t₁ + m) p).S.h_j < j := Nat.lt_of_not_le (hmin m (by omega))
  have hmc : (stateBefore x (t₁ + m + 1) p).S.h_max ≤ j + 1 :=
    le_trans (h_max_mono S Sched x hDiv p (show t₁ + m + 1 ≤ t₂ by omega)) hm
  have hjm1 := h_j_lt_h_max S Sched x (t₁ + m + 1) p
  have hmm := h_max_mono S Sched x hDiv p (show t₁ + m ≤ t₁ + m + 1 by omega)
  have hjm0 := h_j_lt_h_max S Sched x (t₁ + m) p
  have hnc := hNo (t₁ + m) (by omega) (by omega)
  unfold ForkChoiceChangeAt at hnc
  push Not at hnc
  obtain ⟨hroot, hfl⟩ := hnc
  rcases floor_cases (stateBefore x (t₁ + m + 1) p).S with ⟨-, -, hfl1⟩ | ⟨hc1, -⟩
  · -- contested after: a rise
    exfalso
    rw [hfl1] at hfl
    rcases floor_cases (stateBefore x (t₁ + m) p).S with ⟨-, hme0, hfl0⟩ | ⟨-, hfl0⟩
    · rw [hfl0, hme0] at hfl
      unfold Height at *
      omega
    · rw [hfl0] at hfl
      unfold Height at *
      omega
  · have hme1 : (stateBefore x (t₁ + m + 1) p).S.h_max =
        (stateBefore x (t₁ + m + 1) p).S.h_j + 1 := by
      unfold Height at *
      omega
    have hr1 : get_fc_root (stateBefore x (t₁ + m + 1) p).S =
        (stateBefore x (t₁ + m + 1) p).S.J := by
      rcases root_cases (stateBefore x (t₁ + m + 1) p).S with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · rcases h with h | h
        · rw [hc1] at h
          cases h
        · exact absurd hme1 h
    have hr0J : (get_fc_root (stateBefore x (t₁ + m) p).S).AncestorEq
        (stateBefore x (t₁ + m) p).S.J := by
      rcases root_cases (stateBefore x (t₁ + m) p).S with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        exact ancestorEq_refl _
      · rw [h]
        exact F_ancestorEq_J_of_stateBefore S Sched x _ p
    have hJJ : (stateBefore x (t₁ + m + 1) p).S.J.AncestorEq (stateBefore x (t₁ + m) p).S.J := by
      rw [← hr1]
      exact ancestorEq_trans (hroot hr1 hme1) hr0J
    have hj1 : (stateBefore x (t₁ + m + 1) p).S.h_j = j := by
      unfold Height at *
      omega
    have hpc : p ∉ Sched.adv ((t₁ + m + 1 : ℕ) : Int) :=
      fun h => hp (hMono _ _ (by exact_mod_cast (show t₁ + m + 1 ≤ t₂ by omega)) h)
    by_cases h00 : (stateBefore x (t₁ + m) p).S.h_j = 0
    · rw [J_genesis S Sched x _ p h00] at hJJ
      have hg := (GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff _).1 hJJ
      have hj2 : (stateBefore x t₂ p).S.h_j = j := by
        have := h_j_lt_h_max S Sched x t₂ p
        unfold Height at *
        omega
      rw [← J_eq_of_h_j_eq S Sched x hMono hU hRoots tEnd (t₁ + m + 1) t₂ p p hThird (by omega)
        ht₂ hpc hp (hj1.trans hj2.symm) (by omega)]
      exact hg
    · exfalso
      have h1 : 1 ≤ j := by omega
      have hh1 := J_height S Sched x (t₁ + m + 1) p (by rw [hj1]; exact h1)
      have hh0 := J_height S Sched x (t₁ + m) p (Nat.one_le_iff_ne_zero.mpr h00)
      have hmono := (lem47_chain_state_heights S.C _ _).2.2.2.1 hJJ
      rw [hh1, hh0, hj1] at hmono
      unfold Height at *
      omega

/-- **A validator's frame stays compatible with a viable block of another while its fork choice
does not change.** The hypotheses of `root_compatible_of_viable`, and: `w` is honest at `b ≥ t₀`,
`b ≤ tEnd`, and `w` has no `ForkChoiceChangeAt` at any time from `t₀` to before `b`. Then before
`b`: `w`'s `head_height_floor` is at most `W`'s chain-state height, and `w`'s finalized block and
fork-choice root are compatible with `W`.

Why: `head_height_floor` does not rise (`floor_le_of_no_change`, `floor_le_of_viable`). The finalized block,
finalized at a height `f` by the chain state of a block `D`: when `W` is higher than `f`, Lemma 89a;
otherwise `head_height_floor` makes `h_max = f + 1` and `W`'s height `f`, so the finalized block is the
justified block (Lemma 76), and that case is the root's. The root is the finalized block, or the
justified block `J` at a height `j` with `h_max = j + 1`, the state not contested, so `W`'s height
is `j` or `j + 1`. At `j + 1`, `W` is a descendant of `J` (not contested). At `j`: the cache `h_j`
did not pass `j` after `t₀` (`J_genesis_of_cache_passes`, or `J` is the genesis block), so at `t₀`
it was `j` with the justified block `J` (Lemma 76) and `h_max = j + 1`; `w` was not contested then
(its `head_height_floor` would be greater than `W`'s height), so its root then was `J`, compatible with `W`
(`root_compatible_of_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₀ ≤ b`: the times;
  `w`, `u`: the two validators; `W`: the block.

Roots name blocks until `tR`, at least `max (t₀ + Δ S) b`: the proof compares blocks `u` holds
before `t₀ + Δ` and blocks `w` holds before `b`. -/
theorem frame_compatible_of_viable (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd t₀ b : ℕ) (w u : V) (W : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (hEnd : t₀ + Δ S ≤ tEnd)
    (hb : b ≤ tEnd) (ht₀b : t₀ ≤ b) (h1 : 1 ≤ t₀) (hGST : GST ≤ t₀)
    (hw : w ∉ Sched.adv (b : Int))
    (hu : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t₀ + Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hW : W ∈ (fg_to_ac (stateBefore x (t₀ + Δ S) u).S).viable_heads)
    (hWw : W ∈ (stateBefore x t₀ w).S.T)
    (hNo : ∀ t : ℕ, t₀ ≤ t → t < b → ¬ ForkChoiceChangeAt S Sched x w t)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max (t₀ + Δ S) b ≤ tR) :
    head_height_floor (stateBefore x b w).S ≤ (chainStateOf S.C W).h ∧
      (stateBefore x b w).S.F.compatible W = true ∧
      (get_fc_root (stateBefore x b w).S).compatible W = true := by
  have hw₀ : w ∉ Sched.adv (t₀ : Int) := fun h => hw (hMono _ _ (by exact_mod_cast ht₀b) h)
  have hflw₀ := floor_le_of_viable S Sched x GST hDiv hMono hSync hCatch hRoots hParent hU
    tEnd t₀ w u W hThird hEnd hGST hw₀ hu hW (by omega)
  have hflb : head_height_floor (stateBefore x b w).S ≤ (chainStateOf S.C W).h :=
    le_trans (floor_le_of_no_change S Sched x w t₀ b ht₀b hNo) hflw₀
  have hWb : W ∈ (stateBefore x b w).S.T := (stateBefore_grows x hDiv w ht₀b).1 hWw
  have hmb := h_max_le_floor_add_one (stateBefore x b w).S
  have hjb := h_j_lt_h_max S Sched x b w
  -- the justified block at `b`, at the height of `W`, is compatible with `W`
  have JW : (stateBefore x b w).S.h_max = (stateBefore x b w).S.h_j + 1 →
      (chainStateOf S.C W).h = (stateBefore x b w).S.h_j →
      (stateBefore x b w).S.J.compatible W = true := by
    intro hmJ hWj
    have hj0 := h_j_mono S Sched x hDiv hMono hU hRoots tEnd t₀ b w hThird ht₀b hb hw (by omega)
    by_cases hlt : (stateBefore x t₀ w).S.h_j < (stateBefore x b w).S.h_j
    · rw [J_genesis_of_cache_passes S Sched x hDiv hMono hU hRoots tEnd t₀ b
        (stateBefore x b w).S.h_j w hThird ht₀b hb hw hNo hlt le_rfl (by rw [hmJ]) (by omega),
        compatible_iff]
      exact Or.inl (genesis_ancestorEq W)
    have hjeq : (stateBefore x t₀ w).S.h_j = (stateBefore x b w).S.h_j := by
      unfold Height at *
      omega
    have hJJ := J_eq_of_h_j_eq S Sched x hMono hU hRoots tEnd t₀ b w w hThird (by omega) hb hw₀
      hw hjeq (by omega)
    have hm₀ := h_max_mono S Sched x hDiv w ht₀b
    have hj₀ := h_j_lt_h_max S Sched x t₀ w
    have hm₀eq : (stateBefore x t₀ w).S.h_max = (stateBefore x t₀ w).S.h_j + 1 := by
      unfold Height at *
      omega
    have hr₀ : get_fc_root (stateBefore x t₀ w).S = (stateBefore x t₀ w).S.J := by
      rcases root_cases (stateBefore x t₀ w).S with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exfalso
        rcases h with h | h
        · obtain ⟨-, -, hfl'⟩ :=
            GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree _ h
          rw [hfl'] at hflw₀
          unfold Height at *
          omega
        · exact h hm₀eq
    have hc := root_compatible_of_viable S Sched x GST hDiv hMono hSync hCatch hRoots
      hParent hU tEnd t₀ w u W hThird hEnd h1 hGST hw₀ hu hW hWw (by omega)
    rw [hr₀, hJJ] at hc
    exact hc
  -- the finalized block at `b`
  have hF : (stateBefore x b w).S.F.compatible W = true := by
    obtain ⟨D, hD, hFD⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x b) w
    have hSt : stateBefore x b w = x[stepBefore x b][w].st := rfl
    rw [← hSt] at hD hFD
    by_cases hlt : (chainStateOf S.C D).h_F < (chainStateOf S.C W).h
    · rw [hFD, compatible_iff]
      exact Or.inl (finalized_ancestorEq_of_held S Sched x hMono hU hRoots tEnd b t₀ w w D W
        hThird hb (by omega) hw hw₀ hD hWw hlt (by omega))
    push Not at hlt
    by_cases hf0 : (chainStateOf S.C D).h_F = 0
    · rw [hFD, GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D hf0,
        compatible_iff]
      exact Or.inl (genesis_ancestorEq W)
    have hf1 : 1 ≤ (chainStateOf S.C D).h_F := Nat.one_le_iff_ne_zero.mpr hf0
    obtain ⟨-, -, hFDa, -⟩ :=
      (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2 hf1
    have h47 := (lem47_chain_state_heights S.C D D).1
    have hFwD : (stateBefore x b w).S.F.AncestorEq D := by rw [hFD]; exact hFDa
    have hjD := h_j_of_mem_T_of_stateBefore S Sched x _ w D hD hFwD
    rw [σ_eq_of_stateBefore S Sched x _ w D hD] at hjD
    have hjeq : (stateBefore x b w).S.h_j = (chainStateOf S.C D).h_F := by
      unfold Height at *
      omega
    have hFJ := F_eq_J_of_height S Sched x hMono hU hRoots tEnd b b w w D hThird hb hb hw hw hD
      hFD hf1 hjeq (by omega)
    rw [hFJ]
    exact JW (by unfold Height at *; omega) (by unfold Height at *; omega)
  refine ⟨hflb, hF, ?_⟩
  rcases root_cases (stateBefore x b w).S with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · rw [hrJ]
    have hfl : head_height_floor (stateBefore x b w).S = (stateBefore x b w).S.h_j := by
      rcases floor_cases (stateBefore x b w).S with ⟨hc, -, -⟩ | ⟨-, h⟩
      · rw [hcJ] at hc
        cases hc
      · rw [h, hmJ]
        rfl
    have hWh := height_le_h_max S Sched x b w W hWb
    by_cases hWj : (chainStateOf S.C W).h = (stateBefore x b w).S.h_j + 1
    · rw [compatible_iff]
      left
      have hFW := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd b b w w W hThird hb hb hw hw
        hWb (by unfold Height at *; omega) (by omega)
      by_contra hJW
      have hc := fg_contest_true_of (stateBefore x b w).S W hmJ hWb hFW
        (by rw [σ_eq_of_stateBefore S Sched x b w W hWb, hWj, hmJ]) hJW
      rw [hcJ] at hc
      cases hc
    · exact JW hmJ (by rw [hfl] at hflb; unfold Height at *; omega)
  · rw [hrF]
    exact hF

/-- **The frame of a validator with no fork-choice change is compatible with an honest vote's
viable block.** Under the execution assumptions and unforgeability, from `GST` on, with fewer than a
third of the validators in the adversary set up to `tEnd`; write `vt` for the vote time of slot
`σ`: when `u`'s tick at `vt` put `vote` on the wire, `u` is awake and honest from `vt` to
`vt + 2Δ ≤ tEnd` with no `ForkChoiceChangeAt` from `vt` to before `vt + 2Δ`, `w` is awake and
honest from `vt` to `b ≤ tEnd`, `b ≥ vt + Δ`, with no `ForkChoiceChangeAt` from `vt + Δ` to before
`b`, then `vote` is `u`'s slot-`σ` vote for a block `H_u`, and some block `W`, `H_u` or a
descendant of it, held by `w` before `vt + Δ`, is such that before `b`: `w`'s `head_height_floor`
is at most `W`'s chain-state height, and `w`'s finalized block and fork-choice root are compatible
with `W`.

Why: `W` is a viable head of `u` at `vt`, `H_u` or a descendant of `H_u`
(`honest_vote_ancestor_of_viable`), still one at `vt + 2Δ` (`viable_head_kept`); it reaches
`w` by `vt + Δ` (`w`'s finalized block then is compatible with it,
`finalized_compatible_of_viable`), and `frame_compatible_of_viable` from `vt + Δ` to `b`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `b`: the times;
  `σ`: the slot of the vote; `u`: the voter; `w`: the validator whose frame is read; `vote`: the
  vote.

Roots name blocks until `tR`, at least `max (voteTime S σ + 2 * Δ S) b`: the proof keeps `W`
viable at `u` up to `vt + 2Δ` (`viable_head_kept`, read with its end time `vt + 2Δ`) and reads
`w`'s frame before `b`. -/
theorem vote_frame_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd σ b : ℕ) (u w : V) (vote : GoldfishVote V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hEnd : voteTime S σ + 2 * Δ S ≤ tEnd) (hb : b ≤ tEnd) (hbσ : voteTime S σ + Δ S ≤ b)
    (hGST : GST ≤ voteTime S σ)
    (hu : ∀ t' : ℕ, voteTime S σ ≤ t' → t' ≤ voteTime S σ + 2 * Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hNoU : ∀ t : ℕ, voteTime S σ ≤ t → t < voteTime S σ + 2 * Δ S →
      ¬ ForkChoiceChangeAt S Sched x u t)
    (hw : ∀ t' : ℕ, voteTime S σ ≤ t' → t' ≤ b →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hNoW : ∀ t : ℕ, voteTime S σ + Δ S ≤ t → t < b → ¬ ForkChoiceChangeAt S Sched x w t)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max (voteTime S σ + 2 * Δ S) b ≤ tR) :
    ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T, vote = GoldfishVote.mk u σ H_u.root ∧
      ∃ W : Block V, H_u.AncestorEq W ∧ W ∈ (stateBefore x (voteTime S σ + Δ S) w).S.T ∧
        head_height_floor (stateBefore x b w).S ≤ (chainStateOf S.C W).h ∧
        (stateBefore x b w).S.F.compatible W = true ∧
        (get_fc_root (stateBefore x b w).S).compatible W = true := by
  have hΔ := one_le_Δ S
  have hvt := voteTime_eq S σ
  obtain ⟨H_u, hHT, hvote, W, hWv, hHW⟩ := honest_vote_ancestor_of_viable S Sched x σ u vote hSend
  refine ⟨H_u, hHT, hvote, W, hHW, ?_⟩
  have hWv2 := viable_head_kept S Sched x hDiv hMono hU hRoots (voteTime S σ + 2 * Δ S)
    (voteTime S σ)
    u W (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird) hWv (by omega)
    (voteTime S σ + Δ S + Δ S) (by omega) (by omega) (hu _ (by omega) (by omega)).2
    (fun t h1 h2 => hNoU t h1 (by omega))
  have hu' : ∀ t' : ℕ, voteTime S σ + Δ S ≤ t' → t' ≤ voteTime S σ + Δ S + Δ S →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) :=
    fun t' h1 h2 => hu t' (by omega) (by omega)
  have hwb : w ∉ Sched.adv (b : Int) := (hw b (by omega) le_rfl).2
  have hwt₀ : w ∉ Sched.adv ((voteTime S σ + Δ S : ℕ) : Int) := (hw _ (by omega) (by omega)).2
  have hFc := finalized_compatible_of_viable S Sched x GST hDiv hMono hSync hCatch hRoots
    hParent hU tEnd (voteTime S σ + Δ S) w u W hThird (by omega) (by omega) (by omega) hwt₀ hu'
    hWv2 (by omega)
  have hWw : W ∈ (stateBefore x (voteTime S σ + Δ S) w).S.T :=
    mem_T_before_add_delay_of_held hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent
      (t₁ := voteTime S σ) (t := voteTime S σ) (by omega) le_rfl hGST
      (hu _ le_rfl (by omega)).2 ((mem_viable_heads_iff _ _).1 hWv).1
      (fun t' h1 h2 => hw t' h1 (by omega)) hFc
  refine ⟨hWw, frame_compatible_of_viable S Sched x GST hDiv hMono hSync hCatch hRoots
    hParent hU tEnd (voteTime S σ + Δ S) b w u W hThird (by omega) hb hbσ (by omega) (by omega)
    hwb hu' hWv2 hWw hNoW (by omega)⟩

/-- **With no fork-choice change, an honest vote of slot `σ` extends a validator's justified block
when that block is its root at a time `t` at least one delay after the vote.** Under the execution
assumptions and unforgeability, from `GST` on, with fewer than a third of the validators in the
adversary set up to `tEnd`; write `a₀` for the time `2Δ` into slot `σ − 1`: when `u` is awake and
honest from `a₀` to the vote time `vt` of slot `σ` with no `ForkChoiceChangeAt` from the view
freeze of slot `σ − 1` to before `vt`; `w` is awake and honest from `a₀` to `t ≤ tEnd`,
`vt + Δ ≤ t`, with no `ForkChoiceChangeAt` from `a₀` to before `t`; `w`'s state before `t` has
`h_max = h_j + 1` and is not contested, so its root is its justified block; and `u`'s tick at `vt` put
`vote` on the wire — then `vote` is `u`'s slot-`σ` vote for a block `H_u` it holds, and `w`'s
justified block before `t` is `H_u` or an ancestor of `H_u`.

Why (`j` is `w`'s cache `h_j` before `t`, `J` its justified block): `w`'s cache was already `j` at
`a₀`, with the same `J` (`J_genesis_of_cache_passes`, Lemma 76), so `J`'s witness reaches `u` by
the view freeze; `u`'s cache at `vt` is not more than `j` (its witness would reach `w` and raise its
`h_max`), so it is `j` and `u`'s justified block is `J`. Then `u`'s root is `J`, which the vote
extends, or `head_height_floor` at `u` is at least `j + 1`: every viable block of `u` reaches `w`, at the height
`h_max` of `w`, so is a descendant of `J` (not contested), and no strict ancestor of `J` is viable
at `u`; the vote extends `J` (`honest_vote_spec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t`: the times;
  `σ`: the slot of the vote; `u`: the voter; `w`: the validator whose root is read; `vote`: the
  vote.

Roots name blocks until `tR`, at least `t`: every block the proof compares is held by `u` before
`vt` or by `w` before `t`, and `vt + Δ ≤ t` (`viable_head_kept` is read with its end time `vt`). -/
theorem vote_extends_justified_root (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST : ℕ) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (tEnd σ t : ℕ) (u w : V) (vote : GoldfishVote V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hσ : 1 ≤ σ) (hGST : GST ≤ slotStart S (σ - 1) + 2 * Δ S)
    (ht : voteTime S σ + Δ S ≤ t) (hEnd : t ≤ tEnd)
    (hu : ∀ t' : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t' → t' ≤ voteTime S σ →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int))
    (hNoU : ∀ t' : ℕ, viewFreeze S (σ - 1) ≤ t' → t' < voteTime S σ →
      ¬ ForkChoiceChangeAt S Sched x u t')
    (hw : ∀ t' : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t' → t' ≤ t →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hNoW : ∀ t' : ℕ, slotStart S (σ - 1) + 2 * Δ S ≤ t' → t' < t →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hmJ : (stateBefore x t w).S.h_max = (stateBefore x t w).S.h_j + 1)
    (hcJ : fg_contest (stateBefore x t w).S = false)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t ≤ tR) :
    ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
      vote = GoldfishVote.mk u σ H_u.root ∧ (stateBefore x t w).S.J.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ
  have hss : slotStart S σ = slotStart S (σ - 1) + 4 * Δ S := by
    rw [← hσ', slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one, hσ']
  have hfz : viewFreeze S (σ - 1) = slotStart S (σ - 1) + 3 * Δ S := viewFreeze_eq S (σ - 1)
  have hvt : voteTime S σ = slotStart S σ + Δ S := voteTime_eq S σ
  obtain ⟨H_u, hHT, hvote, hρH, hG⟩ := honest_vote_spec S Sched x hDiv σ u vote hSend
  refine ⟨H_u, hHT, hvote, ?_⟩
  set a₀ := slotStart S (σ - 1) + 2 * Δ S with ha₀
  set vt := voteTime S σ with hvt'
  have hwt : w ∉ Sched.adv (t : Int) := (hw t (by omega) le_rfl).2
  have hwa : w ∉ Sched.adv (a₀ : Int) := (hw a₀ le_rfl (by omega)).2
  have huvt : u ∉ Sched.adv (vt : Int) := (hu vt (by omega) le_rfl).2
  set j := (stateBefore x t w).S.h_j with hj
  -- the genesis block is an ancestor of everything
  by_cases hJg : (stateBefore x t w).S.J = Block.genesis
  · rw [hJg]
    exact genesis_ancestorEq H_u
  have hj1 : 1 ≤ j := by
    by_contra h0
    exact hJg (J_genesis S Sched x t w (by rw [← hj]; unfold Height at *; omega))
  -- `w`'s cache was `j` at `a₀`
  have hja := h_j_mono S Sched x hDiv hMono hU hRoots tEnd a₀ t w hThird (by omega) hEnd hwt htR
  have hjaeq : (stateBefore x a₀ w).S.h_j = j := by
    by_contra hne
    exact hJg (J_genesis_of_cache_passes S Sched x hDiv hMono hU hRoots tEnd a₀ t j w hThird
      (by omega) hEnd hwt (fun t' h1 h2 => hNoW t' h1 h2) (by unfold Height at *; omega) le_rfl
      (by rw [hmJ]) htR)
  have hJa := J_eq_of_h_j_eq S Sched x hMono hU hRoots tEnd a₀ t w w hThird (by omega) hEnd hwa
    hwt hjaeq (by omega)
  -- a block held by `u` at `vt` of height greater than `j` reaches `w` and is a descendant of
  -- `w`'s finalized block before `t`
  have hreach : ∀ Y : Block V, Y ∈ (stateBefore x vt u).S.T → j < (chainStateOf S.C Y).h →
      Y ∈ (stateBefore x t w).S.T ∧ (stateBefore x t w).S.F.AncestorEq Y := by
    intro Y hY hYh
    have hjv := h_j_mono S Sched x hDiv hMono hU hRoots tEnd (vt + Δ S) t w hThird ht hEnd hwt htR
    have hY1 := mem_T_of_delivery_high S Sched x GST hDiv hMono hSync hCatch hRoots hParent
      hU tEnd vt u w Y hThird (by omega) (by omega) (by omega) huvt hY
      (fun t' h1 h2 => hw t' (by omega) (by omega)) (by unfold Height at *; omega) (by omega)
    have hYt := (stateBefore_grows x hDiv w ht).1 hY1
    exact ⟨hYt, F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd t t w w Y hThird hEnd hEnd hwt
      hwt hYt (by unfold Height at *; omega) (by omega)⟩
  -- `u`'s cache at `vt` is at most `j`
  have hjuv : (stateBefore x vt u).S.h_j ≤ j := by
    by_contra hgt
    obtain ⟨⟨Yu, hYu, -, hjYu⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x vt u
    have hYuh := (lem47_chain_state_heights S.C Yu Yu).1.2.1
    have hr := (hreach Yu hYu (by unfold Height at *; omega)).1
    have hh := height_le_h_max S Sched x t w Yu hr
    unfold Height at *
    omega
  -- `J`'s witness reaches `u` by the view freeze
  obtain ⟨⟨Y, hY, hJY, hjY⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x a₀ w
  have hYh := (lem47_chain_state_heights S.C Y Y).1.2.1
  have hjuf := h_j_mono S Sched x hDiv hMono hU hRoots tEnd (a₀ + Δ S) vt u hThird (by omega)
    (by omega) huvt (by omega)
  have hYu := mem_T_of_delivery_high S Sched x GST hDiv hMono hSync hCatch hRoots hParent
    hU tEnd a₀ w u Y hThird (by omega) (by omega) hGST hwa hY
    (fun t' h1 h2 => hu t' h1 (by omega)) (by unfold Height at *; omega) (by omega)
  have hYv : Y ∈ (stateBefore x vt u).S.T := (stateBefore_grows x hDiv u (by omega)).1 hYu
  have hFuY := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd vt vt u u Y hThird (by omega)
    (by omega) huvt huvt hYv (by unfold Height at *; omega) (by omega)
  have hjY' := h_j_of_mem_T_of_stateBefore S Sched x _ u Y hYv hFuY
  rw [σ_eq_of_stateBefore S Sched x _ u Y hYv] at hjY'
  have hjueq : (stateBefore x vt u).S.h_j = j := by
    unfold Height at *
    omega
  have hJu := J_eq_of_h_j_eq S Sched x hMono hU hRoots tEnd vt t u w hThird (by omega) hEnd huvt
    hwt (by rw [hjueq]) (by omega)
  -- the cases on `u`'s root
  by_cases hru : get_fc_root (stateBefore x vt u).S = (stateBefore x vt u).S.J
  · rw [← hJu, ← hru]
    exact hρH
  have hm := h_j_lt_h_max S Sched x vt u
  have hflu := floor_of_root_ne_J _ hm hru
  obtain ⟨W₀, hW₀⟩ := frame_has_viable_head S Sched x (viewFreeze S (σ - 1)) u
  have hW₀T : W₀ ∈ (stateBefore x (viewFreeze S (σ - 1)) u).S.T :=
    ((mem_viable_heads_iff _ _).1 hW₀).1
  have hW₀v := viable_head_kept S Sched x hDiv hMono hU hRoots vt (viewFreeze S (σ - 1)) u W₀
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast (show vt ≤ tEnd by omega)) hThird) hW₀
    (by omega) vt (by omega) le_rfl huvt hNoU
  refine hG (viewFreeze S (σ - 1)) W₀ _ hW₀T le_rfl (by omega) hW₀v ?_ ?_
  · intro W hW
    obtain ⟨hWT, -, -, hWfl⟩ := viable_props S Sched x _ u W hW
    have hWh : j < (chainStateOf S.C W).h := by
      rw [hjueq] at hflu
      unfold Height at *
      omega
    obtain ⟨hWt, hFW⟩ := hreach W hWT hWh
    have hWm := height_le_h_max S Sched x t w W hWt
    by_contra hJW
    have hc := fg_contest_true_of (stateBefore x t w).S W hmJ hWt hFW
      (by rw [σ_eq_of_stateBefore S Sched x t w W hWt]; unfold Height at *; omega) hJW
    rw [hcJ] at hc
    cases hc
  · intro B hBJ hne hBv
    obtain ⟨-, -, -, hBfl⟩ := viable_props S Sched x _ u B hBv
    have hBh := (lem47_chain_state_heights S.C B _).2.2.2.1 hBJ
    rw [J_height S Sched x t w hj1] at hBh
    rw [hjueq] at hflu
    unfold Height at *
    omega

/-- `B6Ctx S Sched x GST tGAT tAwakeEnd r s`: B6's hypotheses that its proof reads, and the
negation of its conclusion: no validator outside the adversary set has a `ForkChoiceChangeAt` at a
time from the vote time of slot `s − k − 1` to before the support cutoff of slot `s`.

Roots name blocks until `supportCutoff S s`: the window's end; every reader of the bundle compares
blocks held up to it. -/
structure B6Ctx (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd r s : ℕ) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject
  hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject
  hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s)
  hParent : ParentHeldAtDelivery S Sched x
  hOwner : VotesCastByOwner S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hGST : GST ≤ tGAT
  hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int)
  hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
    ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int)
  hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT)
  hEnd : aR S r ≤ tAwakeEnd
  hk : S.C.k + 1 ≤ s
  hBefore : supportCutoff S s ≤ aR S r
  hAnchor : anchorCW S tGAT ≤ slotStart S (s - S.C.k)
  hNo : ∀ (w : V) (t' : ℕ), voteTime S (s - S.C.k - 1) ≤ t' → t' < supportCutoff S s →
    w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t'

namespace B6Ctx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r s : ℕ}

/-- The window's last support cutoff is in the phase. -/
theorem tEnd (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) : supportCutoff S s ≤ tAwakeEnd :=
  le_trans C.hBefore C.hEnd

/-- The window's slots start after `tGAT`. -/
theorem tGAT_le (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) :
    tGAT ≤ slotStart S (s - S.C.k - 1) := by
  have h := C.hAnchor
  have hk := C.hk
  have hΔ := one_le_Δ S
  have e : slotStart S (s - S.C.k - 1 + 1) = slotStart S (s - S.C.k - 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  rw [show s - S.C.k - 1 + 1 = s - S.C.k by omega] at e
  have h4 : 4 * Δ S ≤ 4 * Δ S * (S.C.k + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rw [anchorCW_eq] at h
  omega

/-- A slot of the window has its committee premise and its duty window in the phase. -/
theorem slot_facts (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) :
    anchorCW S tGAT ≤ slotStart S (σ + 1) ∧ tGAT + Δ S ≤ dutyWindowStart S σ := by
  have h1 : anchorCW S tGAT ≤ slotStart S (σ + 1) :=
    le_trans C.hAnchor (slotStart_mono S (by omega))
  exact ⟨h1, dutyWindowStart_of_anchor S tGAT σ h1⟩

/-- A validator honest at `b` in the phase is awake and honest from any time from `tGAT` on to
`b`. -/
theorem awakeHonest (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) (w : V) {t₁ b : ℕ}
    (h1 : tGAT ≤ t₁) (hb : b ≤ tAwakeEnd) (hw : w ∉ Sched.adv (b : Int)) :
    ∀ t : ℕ, t₁ ≤ t → t ≤ b → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := by
  intro t ht1 ht2
  have hwt : w ∉ Sched.adv (t : Int) := fun h => hw (C.hMono _ _ (by exact_mod_cast ht2) h)
  exact ⟨C.hAwake t (by omega) (by omega) w hwt, hwt⟩

/-- A validator honest at `b` has no fork-choice change from any time from the window's start on to
before `b`, when `b` is at most the support cutoff of slot `s`. -/
theorem noChange (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) (w : V) {t₁ b : ℕ}
    (h1 : voteTime S (s - S.C.k - 1) ≤ t₁) (hb : b ≤ supportCutoff S s)
    (hw : w ∉ Sched.adv (b : Int)) :
    ∀ t : ℕ, t₁ ≤ t → t < b → ¬ ForkChoiceChangeAt S Sched x w t := fun t ht1 ht2 =>
  C.hNo w t (by omega) (by omega) (fun h => hw (C.hMono _ _ (by exact_mod_cast ht2.le) h))

/-- At a slot `σ` of the window with `σ + 1 ≤ s`, the members of slot `σ` are honest active at
`σ`, and they hold more than half of the committee of slot `σ`. -/
theorem members (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 1 ≤ s) :
    roundMembers S Sched (σ + 1) ⊆ honestActiveAt S Sched σ ∧
      (S.P.committee σ).card < 2 * (S.P.committee σ ∩ roundMembers S Sched (σ + 1)).card := by
  obtain ⟨hA, hdw⟩ := C.slot_facts hσ
  have hsub := (roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd σ C.hMono C.hAwake
    (by omega) (le_trans (supportCutoff_mono S hσs) C.tEnd)).1
  exact ⟨hsub, committee_majority_of_committeeSleepiness S Sched (anchorCW S tGAT) σ
    C.hCommittees hA⟩

/-- **An update of a window slot saves only confirmations with an honest supporter.** At a slot
`σ` of the window with `σ + 2 ≤ s`, when the update of slot `σ + 1` on the state of a member `v` of
slot `σ` saves `X`, some honest committee member `u` of slot `σ`, honest active at `σ`, put on the
wire at the vote time of slot `σ` its vote for a block it held, `X` or a descendant of `X`
(`honest_supporter_of_update`). -/
theorem supporter_update (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers S Sched (σ + 1)) (A'' : ACState V)
    (hUpdate : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (σ + 1)) v).A
        ((supportCutoff S (σ + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (σ + 1)) v).S)
      ((supportCutoff S (σ + 1) : ℕ) : Int) (σ + 1) = .ok A'')
    (X : Block V) (hX : A''.saved_confirmation σ = some X) :
    ∃ u ∈ honestActiveAt S Sched σ, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) ∧
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  obtain ⟨hsub, hMaj⟩ := C.members hσ (by omega)
  obtain ⟨-, hdw⟩ := C.slot_facts hσ
  have hΔ := one_le_Δ S
  have hvA := honestActiveAt_window S Sched σ v C.hMono (hsub hv)
  have hdv := dutyWindowStart_le_voteTime S σ
  obtain ⟨u, hu, vote, hsend, H_u, hHT, hvote, hXH⟩ := honest_supporter_of_update S Sched x GST σ v
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hOwner
    (by have := voteTime_eq S σ; have := C.hGST; omega)
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (counting_of_committee_majority S Sched x σ (supportCutoff S (σ + 1))
      (roundMembers S Sched (σ + 1)) v hMaj).2.1
    (fun t h1 h2 => hvA t (le_trans hdv h1) h2) A'' hUpdate X hX
  exact ⟨u, hsub (Finset.mem_inter.1 hu).2, vote, hsend, H_u, hHT, hvote, hXH⟩

/-- **A confirmation saved by a member at a window slot has an honest supporter.** As
`supporter_update`, with the confirmation read on `v`'s state right after the support cutoff of
slot `σ + 1` (`honest_supporter_of_saved`). -/
theorem supporter_saved (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers S Sched (σ + 1)) (X : Block V)
    (hX : (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X) :
    ∃ u ∈ honestActiveAt S Sched σ, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) ∧
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  obtain ⟨hsub, hMaj⟩ := C.members hσ (by omega)
  have hvA := honestActiveAt_window S Sched σ v C.hMono (hsub hv)
  obtain ⟨u, hu, vote, hsend, H_u, hHT, hvote, hXH⟩ := honest_supporter_of_saved S Sched x GST σ v
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hOwner
    (by have := voteTime_eq S σ; have := C.hGST; have := (C.slot_facts hσ).2;
        have := dutyWindowStart_le_voteTime S σ; omega)
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (counting_of_committee_majority S Sched x σ (supportCutoff S (σ + 1))
      (roundMembers S Sched (σ + 1)) v hMaj).2.1
    (fun t h1 h2 => hvA t (le_trans (dutyWindowStart_mono S (Nat.le_succ σ)) h1) h2) X hX
  exact ⟨u, hsub (Finset.mem_inter.1 hu).2, vote, hsend, H_u, hHT, hvote, hXH⟩

/-- **A frame with no change is compatible with the viable block of an honest voter of a window
slot.** At a slot `σ` of the window with `σ + 2 ≤ s`, for an honest active voter `u` of slot `σ`
whose tick put `vote` on the wire, and `w` honest at `b`, from one delay after the vote time of
slot `σ` to the support cutoff of slot `s`: `vote_frame_compatible`. -/
theorem frame (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (u : V) (hu : u ∈ honestActiveAt S Sched σ)
    (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (w : V) (b : ℕ) (hbσ : voteTime S σ + Δ S ≤ b) (hb : b ≤ supportCutoff S s)
    (hw : w ∉ Sched.adv (b : Int)) :
    ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T, vote = GoldfishVote.mk u σ H_u.root ∧
      ∃ W : Block V, H_u.AncestorEq W ∧ W ∈ (stateBefore x (voteTime S σ + Δ S) w).S.T ∧
        head_height_floor (stateBefore x b w).S ≤ (chainStateOf S.C W).h ∧
        (stateBefore x b w).S.F.compatible W = true ∧
        (get_fc_root (stateBefore x b w).S).compatible W = true := by
  have hΔ := one_le_Δ S
  obtain ⟨-, hdw⟩ := C.slot_facts hσ
  have hdv := dutyWindowStart_le_voteTime S σ
  have hvt := voteTime_eq S σ
  have hsc := supportCutoff_eq S (σ + 1)
  have hv1 := voteTime_eq S (σ + 1)
  have hss : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hscs := supportCutoff_mono S (show σ + 1 ≤ s by omega)
  have hvμ := voteTime_mono S hσ
  have huA := honestActiveAt_window S Sched σ u C.hMono hu
  have hu2 : u ∉ Sched.adv ((voteTime S σ + 2 * Δ S : ℕ) : Int) :=
    (huA _ (by omega) (by omega)).2
  exact vote_frame_compatible S Sched x GST C.hDiv C.hMono C.hSync C.hCatch C.hRoots
    C.hParent C.hU tAwakeEnd σ b u w vote C.hThird (by have := C.tEnd; omega)
    (le_trans hb C.tEnd) hbσ (by have := C.hGST; omega)
    (fun t' h1 h2 => huA t' (by omega) (by omega))
    (C.noChange u hvμ (by omega) hu2)
    (C.awakeHonest w (by omega) (le_trans hb C.tEnd) hw)
    (C.noChange w (by omega) hb hw) hSend (by omega)

/-- **Clause 1 of `FrontWindowStable`.** At a slot `s₁` from `s − k − 1` to `s − 2`, every member
`w` of slot `s₁ + 1` satisfies `StepFrameAt` relative to every confirmation `X` a member saved for
a slot `σ` from `s − k − 1` to `s₁`.

Why: `X` has an honest supporter `u` (`supporter_saved`), whose vote is an ancestor of a viable
block `W` of `u` that reaches `w` by the support cutoff of slot `σ` (`frame`). Before the vote time
of slot `s₁ + 1`, `w`'s root is compatible with `W`, so with `X`; when the root is `X` or an
ancestor of it, `W` is viable at `w` and in its voter tree (held before the view freeze of slot
`s₁`). Before the support cutoff of slot `s₁ + 2`, `w`'s finalized block is compatible with `W`,
so with `X`. -/
theorem stepFrame (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {s₁ σ : ℕ}
    (h1 : s - S.C.k - 1 ≤ σ) (h2 : σ ≤ s₁) (h3 : s₁ + 2 ≤ s) (v : V)
    (hv : v ∈ Hon S Sched (σ + 1)) (X : Block V)
    (hX : (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X)
    (w : V) (hw : w ∈ Hon S Sched (s₁ + 1)) :
    StepFrameAt S Sched x X s₁ w := by
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hσμ : s - S.C.k - 1 ≤ σ := by omega
  have hΔ := one_le_Δ S
  have hv' : v ∈ roundMembers S Sched (σ + 1) :=
    (roundMembers_mono S Sched (σ + 1) (σ + 2) tAwakeEnd C.hMono (Nat.le_succ _)
      (le_trans (supportCutoff_mono S (by omega)) C.tEnd)).1 hv
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ := C.supporter_saved hσμ (by omega) v hv' X hX
  have hwb : w ∉ Sched.adv ((supportCutoff S (s₁ + 2) : ℕ) : Int) := (Finset.mem_sdiff.1 hw).2
  have hvt := voteTime_eq S σ
  have hvt1 := voteTime_eq S (s₁ + 1)
  have hsc1 := supportCutoff_eq S (s₁ + 2)
  have hvt2 := voteTime_eq S (s₁ + 2)
  have hss1 : slotStart S (s₁ + 2) = slotStart S (s₁ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₁ + 1)]
    exact Nat.mul_succ _ _
  have hssσ := slotStart_mono S (show σ ≤ s₁ by omega)
  have hss0 : slotStart S (s₁ + 1) = slotStart S s₁ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hsc2 := supportCutoff_mono S h3
  have hwa : w ∉ Sched.adv ((voteTime S (s₁ + 1) : ℕ) : Int) :=
    fun h => hwb (C.hMono _ _ (by exact_mod_cast (show voteTime S (s₁ + 1) ≤
      supportCutoff S (s₁ + 2) by omega)) h)
  have hscσ := supportCutoff_eq S (σ + 1)
  have hvσ1 := voteTime_eq S (σ + 1)
  have hssσ1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have huvt : u ∉ Sched.adv ((voteTime S σ : ℕ) : Int) :=
    (honestActiveAt_window S Sched σ u C.hMono huA (voteTime S σ)
      (dutyWindowStart_le_voteTime S σ) (by omega)).2
  obtain ⟨H₁, hH₁T, hv₁, W₁, hHW₁, hW₁T, hfl₁, -, hr₁⟩ := C.frame hσμ (by omega) u huA vote hsend
    w (voteTime S (s₁ + 1)) (by omega) (by have := supportCutoff_eq S s; omega) hwa
  obtain ⟨H₂, hH₂T, hv₂, W₂, hHW₂, -, -, hF₂, -⟩ := C.frame hσμ (by omega) u huA vote hsend
    w (supportCutoff S (s₁ + 2)) (by omega) hsc2 hwb
  have hroot : ∀ H : Block V, H ∈ (stateBefore x (voteTime S σ) u).S.T →
      vote = GoldfishVote.mk u σ H.root → H = H_u := by
    intro H hH hvH
    rw [hvote] at hvH
    simp only [GoldfishVote.mk.injEq, true_and] at hvH
    exact eq_of_root_eq_held S Sched x C.hMono C.hRoots _ u H H_u huvt hH hHT hvH.symm (by omega)
  rw [hroot H₁ hH₁T hv₁] at hHW₁
  rw [hroot H₂ hH₂T hv₂] at hHW₂
  have hXW₁ := ancestorEq_trans hXH hHW₁
  have hXW₂ := ancestorEq_trans hXH hHW₂
  refine ⟨?_, ?_, ?_⟩
  · exact compatible_symm'
      (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXW₁
        (compatible_symm' (by rw [fc_root_eq]; exact hr₁)))
  · intro hRX tree htree
    have hRX' : (get_fc_root (stateBefore x (voteTime S (s₁ + 1)) w).S).AncestorEq X := by
      rw [← fc_root_eq]; exact hRX
    have hRW := ancestorEq_trans hRX' hXW₁
    have hFW := ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hRW
    have hW₁a : W₁ ∈ (stateBefore x (voteTime S (s₁ + 1)) w).S.T :=
      (stateBefore_grows x C.hDiv w (show voteTime S σ + Δ S ≤ voteTime S (s₁ + 1) by omega)).1
        hW₁T
    refine ⟨W₁, ?_, ?_, hXW₁⟩
    · refine mem_voter_tree_of_held S Sched x C.hDiv (voteTime S σ + Δ S) (s₁ + 1) w W₁
        tree hW₁T ?_ (by omega) hFW htree
      rw [Nat.add_sub_cancel, viewFreeze_eq]
      omega
    · rw [mem_viable_heads_iff, fc_root_eq]
      refine ⟨hW₁a, hFW, hRW, ?_⟩
      rw [σ_eq_of_stateBefore S Sched x _ w W₁ hW₁a]
      exact hfl₁
  · exact compatible_symm'
      (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXW₂
        (compatible_symm' hF₂))

/-- **Every member of a window slot saves a confirmation.** At a slot `σ` from `s − k` with
`σ + 2 ≤ s`, every member `v` of slot `σ` holds right after the support cutoff of slot `σ + 1`
some confirmation of slot `σ`: every honest vote of slot `σ` extends `v`'s finalized block
(`vote_extends_finalized_of_no_change`), so the update saves one (`confirmation_saved_of_votes`).
B5's argument (`window_last_confirmation_exists_of_no_change`) at any member and any such slot. -/
theorem member_saves (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers S Sched (σ + 1)) :
    ∃ D : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some D := by
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hσ1 : 1 ≤ σ := by omega
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ1
  have hss : slotStart S σ = slotStart S (σ - 1) + 4 * Δ S := by
    rw [← hσ', slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one, hσ']
  have hss' : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvσ := voteTime_eq S σ
  have hvσ1 := voteTime_eq S (σ + 1)
  have hb := supportCutoff_eq S (σ + 1)
  have hfz : viewFreeze S (σ - 1) = slotStart S (σ - 1) + 3 * Δ S := viewFreeze_eq S (σ - 1)
  have hμ := voteTime_eq S (s - S.C.k - 1)
  have hμσ := slotStart_mono S (show s - S.C.k - 1 ≤ σ - 1 by omega)
  have hbs := supportCutoff_mono S (show σ + 1 ≤ s by omega)
  have hbEnd : supportCutoff S (σ + 1) ≤ tAwakeEnd := le_trans hbs C.tEnd
  obtain ⟨hsub, hMaj⟩ := C.members (σ := σ) (by omega) (by omega)
  have hvb : v ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv).2
  have hvA := honestActiveAt_window S Sched σ v C.hMono (hsub hv)
  have hdwσ : dutyWindowStart S σ ≤ slotStart S (σ - 1) := by
    have h := dutyWindowStart_succ_le_slotStart S (σ - 1)
    rw [hσ'] at h
    exact h
  have hC1 : ∀ u ∈ S.P.committee σ ∩ roundMembers S Sched (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
        vote = GoldfishVote.mk u σ H_u.root ∧
        (stateBefore x (supportCutoff S (σ + 1)) v).S.F.AncestorEq H_u := by
    intro u hu vote hSend
    have huA := honestActiveAt_window S Sched σ u C.hMono (hsub (Finset.mem_inter.1 hu).2)
    exact vote_extends_finalized_of_no_change S Sched x GST tAwakeEnd σ u v vote C.hDiv C.hMono
      C.hSync C.hCatch (C.hRoots.mono hbs) C.hParent C.hU C.hThird hσ1
      (by have := C.hGST; have := C.tGAT_le; omega) hbEnd hvb
      (fun t h1 h2 => huA t (by omega) (by omega))
      (C.noChange v (by omega) hbs hvb)
      (C.noChange u (by omega) (by omega) (huA _ (by omega) (by omega)).2)
      hSend
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) _ C.hDiv C.hMono
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩) hC1
  exact confirmation_saved_of_votes S Sched x GST σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) H v C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hParent C.hOwner
    (by have := C.hGST; have := C.tGAT_le; omega)
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2, (hH u hu).1, (hH u hu).2.1,
      (hH u hu).2.2⟩)
    (counting_of_committee_majority S Sched x σ (supportCutoff S (σ + 1))
      (roundMembers S Sched (σ + 1)) v hMaj).2.1
    (fun t h1 h2 => hvA t (le_trans (dutyWindowStart_mono S (Nat.le_succ σ)) h1) h2)

/-- **An honest vote of a window slot extends every root read one delay or more after it.** At a
slot `σ` from `s − k` with `σ + 2 ≤ s`, an honest active voter `u` of slot `σ` whose tick put
`vote` on the wire votes for a block `H_u` of which the root of every validator `w` honest at a
time `t` from one delay after the vote time of slot `σ` to the support cutoff of slot `s` is an
ancestor, or which it is: the root is the finalized block (`vote_extends_finalized_at_of_no_change`)
or the justified block (`vote_extends_justified_root`). -/
theorem vote_extends_root (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ}
    (hσ : s - S.C.k ≤ σ) (hσs : σ + 2 ≤ s) (u : V) (hu : u ∈ honestActiveAt S Sched σ)
    (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (w : V) (t : ℕ) (ht : voteTime S σ + Δ S ≤ t) (htb : t ≤ supportCutoff S s)
    (hw : w ∉ Sched.adv (t : Int)) :
    ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
      vote = GoldfishVote.mk u σ H_u.root ∧ (get_fc_root (stateBefore x t w).S).AncestorEq H_u := by
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hσ1 : 1 ≤ σ := by omega
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ1
  have hss : slotStart S σ = slotStart S (σ - 1) + 4 * Δ S := by
    rw [← hσ', slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one, hσ']
  have hvσ := voteTime_eq S σ
  have hfz : viewFreeze S (σ - 1) = slotStart S (σ - 1) + 3 * Δ S := viewFreeze_eq S (σ - 1)
  have hμ := voteTime_eq S (s - S.C.k - 1)
  have hμσ := slotStart_mono S (show s - S.C.k - 1 ≤ σ - 1 by omega)
  have hsc := supportCutoff_mono S (show σ + 1 ≤ s by omega)
  have hsc1 := supportCutoff_eq S (σ + 1)
  have hv1 := voteTime_eq S (σ + 1)
  have hss' : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hdwσ : dutyWindowStart S σ ≤ slotStart S (σ - 1) := by
    have h := dutyWindowStart_succ_le_slotStart S (σ - 1)
    rw [hσ'] at h
    exact h
  have huA := honestActiveAt_window S Sched σ u C.hMono hu
  have hGa : GST ≤ slotStart S (σ - 1) + 2 * Δ S := by
    have := C.hGST; have := C.tGAT_le; omega
  have hNoU := C.noChange u (t₁ := viewFreeze S (σ - 1)) (b := voteTime S σ) (by omega) (by omega)
    (huA _ (by omega) (by omega)).2
  have hNoW := C.noChange w (t₁ := slotStart S (σ - 1) + 2 * Δ S) (b := t) (by omega) htb hw
  rcases root_cases (stateBefore x t w).S with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · obtain ⟨H_u, hHT, hvote, hJH⟩ := vote_extends_justified_root S Sched x GST C.hDiv C.hMono
      C.hSync C.hCatch C.hRoots C.hParent C.hU tAwakeEnd σ t u w vote C.hThird hσ1 hGa
      ht (le_trans htb C.tEnd) (fun t' h1 h2 => huA t' (by omega) (by omega)) hNoU
      (C.awakeHonest w (by have := C.tGAT_le; omega) (le_trans htb C.tEnd) hw) hNoW hmJ hcJ
      hSend htb
    exact ⟨H_u, hHT, hvote, hrJ ▸ hJH⟩
  · obtain ⟨H_u, hHT, hvote, hFH⟩ := vote_extends_finalized_at_of_no_change S Sched x GST tAwakeEnd
      σ t u w vote C.hDiv C.hMono C.hSync C.hCatch (C.hRoots.mono htb) C.hParent C.hU
      C.hThird hσ1
      hGa (le_trans htb C.tEnd) (by omega) hw (fun t' h1 h2 => huA t' (by omega) (by omega)) hNoW
      hNoU hSend
    exact ⟨H_u, hHT, hvote, hrF ▸ hFH⟩

/-- **Clause 2 of `FrontWindowStable`, at a member's own confirmation.** With `s = σ + 2`, every
member `w` of slot `σ + 1` saved a confirmation `D` of slot `σ` (`member_saves`), and its root
before the vote time of slot `σ + 2` is `D` or an ancestor of `D`: every honest vote of slot `σ`
extends that root (`vote_extends_root`), and Lemma 78 at `w`. -/
theorem rootChain (C : B6Ctx S Sched x GST tGAT tAwakeEnd r s) {σ : ℕ} (hs : s = σ + 2)
    (w : V) (hw : w ∈ Hon S Sched (σ + 1)) :
    ∃ D : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) w).A.saved_confirmation σ = some D ∧
      (get_fc_root (stateBefore x (voteTime S (σ + 2)) w).S).AncestorEq D := by
  subst hs
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hσ : σ + 2 - S.C.k ≤ σ := by omega
  have hw' : w ∈ roundMembers S Sched (σ + 1) :=
    (roundMembers_mono S Sched (σ + 1) (σ + 2) tAwakeEnd C.hMono (Nat.le_succ _) C.tEnd).1 hw
  obtain ⟨D, hD⟩ := C.member_saves hσ le_rfl w hw'
  refine ⟨D, hD, ?_⟩
  obtain ⟨hsub, hMaj⟩ := C.members (σ := σ) (by omega) (by omega)
  have hwb : w ∉ Sched.adv ((supportCutoff S (σ + 2) : ℕ) : Int) := (Finset.mem_sdiff.1 hw).2
  have hsc2 := supportCutoff_eq S (σ + 2)
  have hwv : w ∉ Sched.adv ((voteTime S (σ + 2) : ℕ) : Int) :=
    fun h => hwb (C.hMono _ _ (by exact_mod_cast (show voteTime S (σ + 2) ≤
      supportCutoff S (σ + 2) by omega)) h)
  have hvσ := voteTime_eq S σ
  have hv2 := voteTime_eq S (σ + 2)
  have hss2 : slotStart S (σ + 2) = slotStart S σ + 8 * Δ S := by
    rw [slotStart_eq, slotStart_eq S σ, Nat.mul_add]
    omega
  have hC1 : ∀ u ∈ S.P.committee σ ∩ roundMembers S Sched (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
        vote = GoldfishVote.mk u σ H_u.root ∧
        (get_fc_root (stateBefore x (voteTime S (σ + 2)) w).S).AncestorEq H_u :=
    fun u hu vote hSend => C.vote_extends_root hσ le_rfl u (hsub (Finset.mem_inter.1 hu).2) vote
      hSend w (voteTime S (σ + 2)) (by omega) (by omega) hwv
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) _ C.hDiv C.hMono
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩) hC1
  have hvA := honestActiveAt_window S Sched σ w C.hMono (hsub hw')
  have hsc1 := supportCutoff_eq S (σ + 1)
  have hv1 := voteTime_eq S (σ + 1)
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hFB : (stateBefore x (supportCutoff S (σ + 1)) w).S.F.compatible
      (get_fc_root (stateBefore x (voteTime S (σ + 2)) w).S) = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (stateBefore_grows x C.hDiv w (show supportCutoff S (σ + 1) ≤ voteTime S (σ + 2) by
        omega)).2.1 (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w)))
  have hGσ : GST ≤ voteTime S σ := by
    have := C.hGST
    have := C.tGAT_le
    have := slotStart_mono S (show σ + 2 - S.C.k - 1 ≤ σ by omega)
    omega
  exact lem78_update_confirmation_extends_voter_majority_chain S Sched x GST σ
    (S.P.committee σ ∩ roundMembers S Sched (σ + 1)) H _ w C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (supportCutoff_mono S (by omega))) C.hParent C.hOwner hGσ
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2, (hH u hu).1, (hH u hu).2.1,
      (hH u hu).2.2⟩)
    (counting_of_committee_majority S Sched x σ (supportCutoff S (σ + 1))
      (roundMembers S Sched (σ + 1)) w hMaj).2.1
    (fun t h1 h2 => hvA t (le_trans (dutyWindowStart_mono S (Nat.le_succ σ)) h1) h2) hFB D hD

end B6Ctx

/-- **B6, the stability fact.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: by contradiction. With no validator outside the adversary set having a
`ForkChoiceChangeAt` from the vote time of slot `s − k − 1` to before the support cutoff of slot
`s`, the two clauses of `FrontWindowStable` hold (`B6Ctx.stepFrame`, `B6Ctx.rootChain`),
against `hFail`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  phase; `r`: the round; `s`: the honest round opening slot.

Roots name blocks until `supportCutoff S s`: every block the proof compares is held before the
support cutoff of slot `s`, the window's end (the bundle `B6Ctx` carries the premise at that
time). -/
theorem stability_fact3 (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r s : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hk : S.C.k + 1 ≤ s)
    (hBefore : supportCutoff S s ≤ aR S r)
    (hAnchor : anchorCW S tGAT ≤ slotStart S (s - S.C.k))
    (hFail : ¬ FrontWindowStable S Sched x (Hon S Sched) (s - 2 * S.C.k) (s - 1)) :
    ∃ (w : V) (t' : ℕ), voteTime S (s - S.C.k - 1) ≤ t' ∧ t' < supportCutoff S s ∧
      w ∉ Sched.adv (t' : Int) ∧ ForkChoiceChangeAt S Sched x w t' := by
  by_contra hcon
  have hNo : ∀ (w : V) (t' : ℕ), voteTime S (s - S.C.k - 1) ≤ t' → t' < supportCutoff S s →
      w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t' :=
    fun w t' h1 h2 h3 h4 => hcon ⟨w, t', h1, h2, h3, h4⟩
  have C : B6Ctx S Sched x GST tGAT tAwakeEnd r s :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hOwner, hU, hGST, hThird, hAwake,
      hCommittees, hEnd, hk, hBefore, hAnchor, hNo⟩
  have hk2 := S.C.k_ge_two
  apply hFail
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 2 := ⟨s - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · intro s₁ h1 h2 σ' hσ1 hσ2 v hv X hX w hw
    exact C.stepFrame (s₁ := s₁) (σ := σ') (by omega) hσ2 (by omega) v hv X hX w hw
  · intro w hw
    rw [show σ + 2 - 1 = σ + 1 from rfl] at hw ⊢
    obtain ⟨D, hD, hRD⟩ := C.rootChain rfl w hw
    exact ⟨D, Or.inr ⟨w, hw, hD⟩, hRD⟩

end GoldilocksCorrectness.Proofs.Executions
