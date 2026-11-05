module
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily

@[expose] public section

/-!
# The voter frame after the hand-over

The proofs of the two facts stated in
`GoldilocksCorrectness/Statements/Executions/HealedVoterFrameStatements.lean`:

- `chain_block_held_before_freeze`: a block on the honest chain before slot `s` is held by every
  honest active voter of slot `s` before the view freeze of slot `s − 1`, when its finalized block
  there is compatible with the block;
- `voterFrame_after_handover`: after the hand-over, every honest active voter of slot `s` has the
  frame `VoterFrameOnChainAt` relative to the honest chain before `s`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff one_le_Δ
  slot_le_of_supportCutoff_lt supportCutoff_mono times_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)
open GoldilocksCorrectness.Statements.Routines (lem66_chain_state_certified lem67_first_advance)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **A block on the honest chain before `s` is held by an honest active voter of `s` before the
view freeze of slot `s − 1`.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot; `w`: the voter; `B`:
  the block.

Roots name blocks until `viewFreeze S (s - 1)`: the confirmation the updater holds reaches `w` by
the view freeze of slot `s − 1`, one delay after the support cutoff of slot `s − 1`
(`mem_T_before_add_delay_of_held_at`). -/
theorem chain_block_held_before_freeze (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s : ℕ) (w : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (viewFreeze S (s - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hw : w ∈ honestActiveAt S Sched s)
    (hB : OnHonestChainBefore S Sched x s₀ s B)
    (hF : (stateBefore x (viewFreeze S (s - 1)) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (viewFreeze S (s - 1)) w).S.T := by
  obtain ⟨μ, hμs, hμ₀, u, hu, C, hC, hBC⟩ := hB
  -- `B` an ancestor of the finalized block: held already
  rcases (compatible_iff _ _).1 hF with hFB | hBF
  swap
  · exact ancestors_mem_T_of_exec S Sched x _ w _ B
      (lem11_node_invariant S Sched x _ w).1.2.2.2.1 hBF
  have hk := S.C.k_ge_two
  obtain ⟨-, hcμ, -, -, hΔ⟩ := times_eq S μ
  obtain ⟨hvs1, hcs1, hfs1, hss1, -⟩ := times_eq S (s - 1)
  have hs1 : s - 1 + 1 = s := by omega
  rw [hs1] at hss1
  obtain ⟨-, hcs, -, -, -⟩ := times_eq S s
  obtain ⟨-, hcs', -, -, -⟩ := times_eq S (s + 1)
  obtain ⟨-, -, -, hss', -⟩ := times_eq S s
  -- the updater `u`
  rw [updaterAt, Finset.mem_sdiff, mem_awakeThroughout_iff] at hu
  have huv : ∀ t : ℕ, dutyWindowStart S (μ + 1) ≤ t → t ≤ supportCutoff S (μ + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    ⟨hu.1 t (by exact_mod_cast h1) (by exact_mod_cast h2),
      fun ha => hu.2 (hMono _ _ (by exact_mod_cast h2) ha)⟩
  have hCT := saved_confirmation_mem_T_supportCutoff S Sched x μ u C hDiv hMono huv hC
  -- `w` awake and honest from the support cutoff of slot `s − 1` to the view freeze of `s − 1`
  rw [honestActiveAt, Finset.mem_sdiff, activeAt, mem_awakeThroughout_iff] at hw
  have hdw : dutyWindowStart S s ≤ supportCutoff S (s - 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  have hμs' : μ ≤ s - 1 := by omega
  have hcm : supportCutoff S μ ≤ supportCutoff S (s - 1) := supportCutoff_mono S hμs'
  have hvf : viewFreeze S (s - 1) = supportCutoff S (s - 1) + Δ S := by omega
  have hww : ∀ t' : ℕ, supportCutoff S (s - 1) ≤ t' → t' ≤ supportCutoff S (s - 1) + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int) := fun t' h1 h2 =>
    ⟨hw.1 t' (by exact_mod_cast le_trans hdw h1) (by omega),
      fun ha => hw.2 (hMono _ _ (by omega) ha)⟩
  have hu₁ : u ∉ Sched.adv ((x[stepBefore x (supportCutoff S μ)].time : ℕ) : Int) := by
    intro ha
    apply hu.2
    refine hMono _ _ ?_ ha
    have h1 := time_stepBefore_add_one x hDiv (show 1 ≤ supportCutoff S μ by omega)
    have h2 : supportCutoff S μ ≤ supportCutoff S (μ + 1) := supportCutoff_mono S (by omega)
    have h3 : x[stepBefore x (supportCutoff S μ)].time ≤ supportCutoff S (μ + 1) := by omega
    exact_mod_cast h3
  have hGST' : GST ≤ supportCutoff S (s - 1) := by
    have := supportCutoff_mono S (show s₀ ≤ s - 1 by omega)
    obtain ⟨hv0, hc0, -, -, -⟩ := times_eq S s₀
    omega
  rw [hvf]
  have hCw : C ∈ (stateBefore x (supportCutoff S (s - 1) + Δ S) w).S.T := by
    refine mem_T_before_add_delay_of_held_at hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hParent hcm hGST' hu₁ hCT hww ?_
    rw [← hvf]
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFB hBC))
  exact ancestors_mem_T_of_exec S Sched x _ w C B hCw hBC

/-- **The voter frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.

Roots name blocks until `voteTime S s`: the proof reads `w`'s state before the vote time of slot
`s` (Lemma 91f, and the entry the certificate names against `w`'s justified block), and the blocks
of the chain `w` holds by the view freeze of slot `s − 1`.

Caches up to `voteTime S s`: the proof reads `w`'s caches before the vote time of slot `s` (Lemma
91 (d) and (f) there). -/
theorem voterFrame_after_handover_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ i₂ H s : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x[i₂].time < viewFreeze S (s - 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hw : w ∈ honestActiveAt S Sched s) :
    VoterFrameOnChainAt S Sched x s₀ s w := by
  intro B hB
  have hΔ := one_le_Δ S
  have hs1 : 1 ≤ s := by obtain ⟨μ, hμ, -⟩ := hB; omega
  obtain ⟨hvs, hcs, -, -, -⟩ := times_eq S s
  obtain ⟨-, -, hfs1, hss1, -⟩ := times_eq S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  obtain ⟨-, hcs', -, hss', -⟩ := times_eq S s
  obtain ⟨-, hcs'', -, -, -⟩ := times_eq S (s + 1)
  have hvf : viewFreeze S (s - 1) ≤ voteTime S s := by omega
  -- the reading step before the vote time of slot `s`
  obtain ⟨jw, hjw⟩ : ∃ jw, jw = stepBefore x (voteTime S s) := ⟨_, rfl⟩
  have htw : x[jw].time + 1 = voteTime S s := by
    rw [hjw]; exact time_stepBefore_add_one x hDiv (by omega)
  have hstw : stateBefore x (voteTime S s) w = x[jw][w].st := by unfold stateBefore; rw [hjw]
  have hw' := hw
  rw [honestActiveAt, Finset.mem_sdiff] at hw'
  have hwj : w ∉ Sched.adv (x[jw].time : Int) := by
    intro ha
    apply hw'.2
    refine hMono _ _ ?_ ha
    have h3 : x[jw].time ≤ supportCutoff S (s + 1) := by omega
    exact_mod_cast h3
  have hiw : x[i₂].time ≤ x[jw].time := by omega
  have hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[jw].time → s_a < s := fun s_a h => by
    have := (slot_le_of_supportCutoff_lt S s_a s).1 (by omega)
    omega
  -- the root is on the chain before `s` (Lemma 91 (f))
  have hR := lem91f_voter_root_on_chain_before_until S Sched x s₀ i₂ jw s H w hDiv hMono
    (hRoots.mono (by omega)) hU hAdvQ hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hiw hwj hs'
  rw [← hstw] at hR
  refine ⟨onHonestChainBefore_compatible S Sched x s₀ s _ B hChain hR hB, fun hRB tree htree => ?_⟩
  have hRB' : (get_fc_root (stateBefore x (voteTime S s) w).S).AncestorEq B := by
    rw [← fc_root_eq]; exact hRB
  -- the state is not contested, and the floor is `h_max − 1` (Lemma 91 (d))
  have hfl := (lem91d_not_contested_until S Sched x s₀ i₂ jw s H w hDiv hMono hU hAdvQ hChain hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hiw hwj hs').2
  rw [← hstw] at hfl
  -- the finalized block before the view freeze of slot `s − 1` is an ancestor of `B`
  have hFB : (stateBefore x (viewFreeze S (s - 1)) w).S.F.AncestorEq B :=
    ancestorEq_trans (stateBefore_grows x hDiv w hvf).2.1
      (ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hRB')
  have hheld : ∀ D : Block V, OnHonestChainBefore S Sched x s₀ s D → B.AncestorEq D →
      D ∈ (stateBefore x (viewFreeze S (s - 1)) w).S.T := fun D hD hBD =>
    chain_block_held_before_freeze S Sched x GST s₀ s w D hDiv hMono hSync hCatch
      (hRoots.mono hvf) hParent hGST hw hD
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFB hBD)))
  -- a block of the chain before `s` at a chain-state height at least `h_max − 1`
  obtain ⟨E, hE, hEh⟩ : ∃ E : Block V, OnHonestChainBefore S Sched x s₀ s E ∧
      (stateBefore x (voteTime S s) w).S.h_max - 1 ≤ (chainStateOf S.C E).h := by
    rw [hstw]
    by_cases hM : (x[jw][w].st).S.h_max ≤ H + 1
    · -- the justified block, on the chain at the height `h_j > H`
      obtain ⟨hH, -, -, hJh, -⟩ := hCaches jw w hiw (by omega) hwj
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x jw w
      have h1 : 1 ≤ (chainStateOf S.C D).h_j := by
        rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
      obtain ⟨hJC, -, -⟩ := (lem66_chain_state_certified S.C D).1 h1
      rw [← hJD, ← hhjD] at hJC
      obtain ⟨s_a, E, hcut, hAt, -, -, hEr⟩ := cert_entry_at_slot S Sched x s₀ H jw w D _ _ hDiv
        hMono hU (hAdvQ _) hOld hD (progressCertOn_of_justificationCertOn hJC) hH
      have hJmem : (x[jw][w].st).S.J ∈ (x[jw][w].st).S.T :=
        (lem11_node_invariant S Sched x jw w).1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
      have hEJ : E = (x[jw][w].st).S.J :=
        hRoots E _ (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hAt (by omega))
          ⟨jw, w, hwj, by omega, hJmem⟩ hEr.symm
      refine ⟨E, ⟨s_a, hs' s_a hcut, hAt⟩, ?_⟩
      rw [hEJ, hJh]
      omega_nat
    · -- the entry at `h_max − 1` named by the certificate of the block that raised the chain
      obtain ⟨-, ⟨Z, hZ, hZh⟩, -⟩ := cachesWitnessed_of_exec S Sched x jw w
      obtain ⟨Y, hYZ, -, -, -, -, hPC⟩ := lem67_first_advance S.C Z ((x[jw][w].st).S.h_max - 1)
        (by omega_nat) (by rw [hZh]; omega_nat)
      have hYT : Y ∈ (x[jw][w].st).S.T := ancestors_mem_T_of_exec S Sched x jw w Z Y hZ hYZ
      obtain ⟨s_a, E, hcut, hAt, -, hEh, -⟩ := cert_entry_at_slot S Sched x s₀ H jw w Y _ _ hDiv
        hMono hU (hAdvQ _) hOld hYT hPC (by omega_nat)
      exact ⟨E, ⟨s_a, hs' s_a hcut, hAt⟩, by rw [hEh]⟩
  -- the candidate: the later of `B` and `E`
  obtain ⟨W, hWc, hBW, hWh⟩ : ∃ W : Block V, OnHonestChainBefore S Sched x s₀ s W ∧
      B.AncestorEq W ∧
      (stateBefore x (voteTime S s) w).S.h_max - 1 ≤ (chainStateOf S.C W).h := by
    rcases (compatible_iff _ _).1 (onHonestChainBefore_compatible S Sched x s₀ s B E hChain hB hE)
      with h | h
    · exact ⟨E, hE, h, hEh⟩
    · exact ⟨B, hB, ancestorEq_refl B, le_trans hEh (chainStateOf_height_mono S.C h)⟩
  obtain ⟨hWt, hWv⟩ := proposal_viable_head_at S Sched x (viewFreeze S (s - 1)) s w W _ _ tree
    hDiv (hheld W hWc hBW) le_rfl hvf ⟨rfl, rfl⟩ (ancestorEq_trans hRB' hBW)
    (by rw [hfl]; exact hWh) htree
  exact ⟨W, hWt, hWv, hBW⟩

/-- **The voter frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.

Roots name blocks until `voteTime S s`: the proof reads `w`'s state before the vote time of slot
`s` (Lemma 91f, and the entry the certificate names against `w`'s justified block), and the blocks
of the chain `w` holds by the view freeze of slot `s − 1`.

It is `voterFrame_after_handover_until` with the caches restricted to the steps it reads. -/
theorem voterFrame_after_handover (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ i₂ H s : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x[i₂].time < viewFreeze S (s - 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hw : w ∈ honestActiveAt S Sched s) :
    VoterFrameOnChainAt S Sched x s₀ s w :=
  voterFrame_after_handover_until S Sched x GST s₀ i₂ H s w hDiv hMono hSync hCatch hRoots
    hParent hU hAdvQ hGST hOld (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hs hChain hw

end GoldilocksCorrectness.Proofs.Executions
