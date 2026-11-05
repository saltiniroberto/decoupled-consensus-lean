module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rQuietRound
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89fUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityB6UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseChainUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89QuietJUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89QuietJUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: part B of Lemma 89 with the delivery
premises up to a bound, namely the front's step to the slot before an honest round opening slot, two
more readers of `B6CtxUpTo`, the bundle `WinCtxUpTo` of an honest round opening slot's window with
its readers, the bundle `QuietCtxUpTo` of B10's hypotheses with its readers, and B11
(`quiet_top_gives_attestation_cutoff_upTo`). The page's routine-level theorems are the facts' fields
or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (delivery_of_round dutyWindowStart_le_voteTime
  dutyWindowStart_mono dutyWindowStart_of_anchor dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slotStart_mono supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq
  voteTime_mono voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (quorum_le_of_phase_set r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject
  healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The chain at the slot before the opening, for the live locks and the confirmations before
it.** Under `FrontHyps` with `s' = m + 1 ≥ s_w + 2k − 1`: every block on the chain of a live lock a
member of `Hon m` holds before the vote time of slot `m + 1`, or of a confirmation of slot `m` a
member of `Hon (m + 1)` saved, satisfies `HonestChainExtends` at `Hon (m + 1)` at slot `m + 1`.

Why: `lem89fq_front`'s last step, kept before its conclusion: `front_locks_chain` at slot `m`,
then the phase step `lem89s_phase_step` from `m` to `m + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `m`: the slot before `s'`.

Restated with the delivery premises up to `M.supportCutoff S.C s'`: the bound of the bundle
`FrontHypsUpTo`.

Read aloud: every block on the chain of a live lock of slot `m` or of a confirmation of slot `m`
satisfies the honest chain invariant at slot `m + 1`. -/
theorem front_step_family_upTo (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    {Δs : ℕ} {ΔNet : ℕ} (H : FrontHypsUpTo M S A x GST tGAT tAwakeEnd s_w s' Hon Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (m : ℕ) (hm : s' = m + 1)
    (hs' : s_w + 2 * S.C.k - 1 ≤ s') :
    ∀ C : Block V, (liveLockAncestors M S A x (Hon m) m C ∨ ∃ v ∈ Hon (m + 1), ∃ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (m + 1))).savedConfirmation m = some C' ∧
        C.AncestorEq C') →
      HonestChainExtends M S A x (Hon (m + 1)) C (m + 1) := by
  subst hm
  have hk := S.C.k_ge_two
  have hb₀ : (s_w + 2 * S.C.k - 2) + 2 = s_w + 2 * S.C.k := by omega
  have hm := (front_locks_chain_upTo M F U R H.E) H (s_w + 2 * S.C.k - 2) hb₀ (m - (s_w + 2 * S.C.k - 2)) (by omega)
  rw [show s_w + 2 * S.C.k - 2 + (m - (s_w + 2 * S.C.k - 2)) = m by omega] at hm
  exact ((lem89s_phase_step_upTo M F U) S A x R GST m (Hon m) (Hon (m + 1))
    (liveLockAncestors M S A x (Hon m) m) H.E H.hNet H.hSkew H.hRedeliver H.Sy H.hΔs
    H.hRoots H.hRootsTick H.hParent H.hOwner (H.gstSync M F U _ (by omega) (by omega))
    (H.honestActive M F H.E U m R (by omega) (by omega))
    (H.honestActive M F H.E U (m + 1) R (by omega) le_rfl) (H.hHonMono m (by omega) (by omega))
    (H.hCommittees m (by omega) (by omega)) (H.hCommittees (m + 1) (by omega) le_rfl) hm
    (fun u hu => (liveLocksOnFamilyAt_of_live M F U) S A x R H.E _ m u
      (fun e he hl => ⟨u, hu, e, he, hl, ancestorEq_refl e.B⟩))
    ((front_step_frames_upTo M F U R H.E) H (s_w + 2 * S.C.k - 2) hb₀ m (by omega) (by omega))).1
namespace B6CtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r s : ℕ}

/-- **A member's confirmation has a viable head of every honest frame on its chain.** At a slot
`σ` from `s − k − 1` with `σ + 2 ≤ s`, for a confirmation `X` of slot `σ` that a member `v` of slot
`σ` saved and a block `Y` that is `X` or an ancestor of `X`: every validator `p` honest at a time
`b` from two delays after the vote time of slot `σ` to the support cutoff of slot `s`, and ticking at or after
`b` to a clock value at most that cutoff, has, before `b`, a viable head of its frame that is `Y` or a descendant of `Y`.

Why: `X` has an honest committee supporter `u` (`supporter_saved`), whose vote's block `H_u` is
`X` or a descendant of `X` and an ancestor of a block `W` that `p` holds, with `p`'s root before
`b` compatible with `W` and its `head_height_floor` at most `W`'s height (`frame`, whose bound on `b` is two delays
after the vote time: `W` reaches `p` by its tick to one delay after it). When the root
is an ancestor of `W`, `W` is a viable head; otherwise `W` is an ancestor of the root, which is an
ancestor of every viable head.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `σ`: the slot; `v`: the member; `X`, `Y`: the blocks; `p`: the validator; `b`:
  the time.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: every validator honest at a time `b` of the window has a viable head on the chain of a
member's confirmation. -/
theorem frameP_of_conf (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers M S A x (σ + 1)) (X Y : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X)
    (hYX : Y.AncestorEq X) (p : V) (b : ℕ) (hb1 : M.voteTime S.C σ + 2 * Δ S ≤ b)
    (hb2 : b ≤ M.supportCutoff S.C s) (hp : p ∉ A.corruptedAtTime x b)
    -- `p` ticks, at or after the real time `b`, to a clock value at most the support cutoff of slot `s`
    (kp cp : ℕ) (hkp : x.lbl kp = Event.tick p cp) (hcp : cp ≤ M.supportCutoff S.C s) (hbkp : (b : ℝ) ≤ x.time kp) :
    ∃ W ∈ (M.fg_to_ac (x.stateBefore b p)).tree,
      W ∈ (M.fg_to_ac (x.stateBefore b p)).viable_heads ∧ Y.AncestorEq W := by
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hcE : M.supportCutoff S.C s ≤ tAwakeEnd := C.tEnd M F
  have hvtσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hcσ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hσs
  have hcs1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ ≤ s by omega)
  have hsync := (C.syncStart M F U) hσ
  have hmx1 := le_max_left (Δ S) Δs
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ :=
    (C.supporter_saved M F R C.E U) hσ hσs v hv X hX
  obtain ⟨H₁, hH₁T, hv₁, W₁, hHW₁, hW₁T, hfl₁, -, hr₁⟩ :=
    (C.frame M F R U Fx) hσ hσs u huA vote hsend p b hb1 hb2 hp kp cp hkp hcp hbkp
  -- `vote` names one block of `u`'s tree at its tick
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hsend
    exact x.lbl_tickStep ⟨i, hi⟩
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := C.E.not_mem_corrupted_of_tick hkU
  have hkUs : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
    have h := (C.E.tick_active _ u _ hkU).2.2
    have : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + Δ S ≤ M.supportCutoff S.C s by omega)
    linarith
  have hH : H₁ = H_u := by
    rw [hvote] at hv₁
    simp only [GoldfishVote.mk.injEq, true_and] at hv₁
    exact C.hRoots _ u _ hkU (by omega) H₁ H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (v := u) huk le_rfl hH₁T) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (v := u) huk le_rfl hHT) hv₁.symm
  rw [hH] at hHW₁
  have hYW := ancestorEq_trans hYX (ancestorEq_trans hXH hHW₁)
  -- `p` ticks to one delay after the vote time before `b`, so `W₁` is in its tree before `b`
  have hpA := (C.awakeHonest M F) R C.E p (t₁ := tGAT) (b := b) le_rfl (le_trans hb2 hcE) hp
  have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) := by
    exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C σ + Δ S by omega)
  have h2R : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) + Δ S ≤ (b : ℝ) := by
    exact_mod_cast (show M.voteTime S.C σ + Δ S + Δ S ≤ b by omega)
  have hkP := (tickStep_spec M) x R C.E (t := M.voteTime S.C σ + Δ S) (v := p) (by omega)
    (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hpA)
  have hkPb : x.tickStep p (M.voteTime S.C σ + Δ S) ≤ x.stepBefore b := by
    by_contra hc
    have h := htime (show x.stepBefore b + 1 ≤ x.tickStep p (M.voteTime S.C σ + Δ S) by omega)
    have hsb := ((stepBefore_time M) x R C.E (show 1 ≤ b by omega)).2
    linarith [hkP.2.2]
  have hW₁b : W₁ ∈ (x.stateBefore b p).tree := (mem_T_mono M F) x R C.E p hkPb hW₁T
  have hinv := (nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R C.E le_rfl hp
  rcases (compatible_iff _ _).1 hr₁ with hRW | hWR
  · have hFW := ancestorEq_trans
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R C.E _ p) hRW
    refine ⟨W₁, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW₁b, hFW⟩, ?_, hYW⟩
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hinv]
    exact ⟨hW₁b, hFW, by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hRW, hfl₁⟩
  · obtain ⟨W', hW'⟩ := (GoldilocksCorrectness.Record.Statements.Executions.frame_has_viable_head M F) S A x R C.E b p
    have hW'' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hinv _).1 hW'
    have hRW' := hW''.2.2.1
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hRW'
    exact ⟨W', ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW''.1, hW''.2.1⟩, hW',
      ancestorEq_trans hYW (ancestorEq_trans hWR hRW')⟩


/-- **`frameP_of_conf` with `p`'s frame read at its step `i`** (rule R3). At a slot `σ` from `s − k − 1` with
`σ + 2 ≤ s`, for a confirmation `X` of slot `σ` that a member `v` of slot `σ` saved and a block `Y` that is `X` or an
ancestor of `X`: every validator `p` honest at a time `b` from two delays after the vote time of slot `σ` to the support
cutoff of slot `s`, read at a step `i` of it at or after its last step before two delays after that vote time, honest
there, with no `ForkChoiceChangeStep` from that step to before `i`, and roots naming blocks up to the real time of `i`,
has at `i` a viable head of its frame that is `Y` or a descendant of `Y`.

Why: `frameP_of_conf`'s argument, with `frame_st` in place of `frame`; `W` reaches `p` by its tick to one delay after the
vote time, a step at most `i`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `σ`: the slot; `v`: the member; `X`, `Y`: the blocks; `p`: the validator; `b`: the time; `i`: the
  step of `p`; `tR`: the bound of the roots.

Read aloud: every validator honest in the window, read at a step with no fork-choice change since two delays after the
vote time of slot `σ`, has there a viable head on the chain of a member's confirmation of slot `σ`. -/
theorem frameP_of_conf_st (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers M S A x (σ + 1)) (X Y : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X)
    (hYX : Y.AncestorEq X) (p : V) (b : ℕ) (hb1 : M.voteTime S.C σ + 2 * Δ S ≤ b)
    (hb2 : b ≤ M.supportCutoff S.C s) (hp : p ∉ A.corruptedAtTime x b)
    -- `p` is read at its step `i`: honest there, at or after its last step before `vt + 2Δ`, with no
    -- `ForkChoiceChangeStep` from that step to before `i`, and roots name blocks up to `tR` (`frame_st`)
    (i : ℕ) (hi : x.time i ≤ tAwakeEnd) (hi₀ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ i)
    (hpi : p ∉ A.corrupted i)
    (hNoP : ∀ j : ℕ, x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ j → j < i → ¬ ForkChoiceChangeStep M S A x p j)
    {tR : ℝ} (hRootsR : RootsNameBlocksUntil M A x tR) (htRi : x.time i ≤ tR) :
    ∃ W ∈ (M.fg_to_ac (x.st i p)).tree,
      W ∈ (M.fg_to_ac (x.st i p)).viable_heads ∧ Y.AncestorEq W := by
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hcE : M.supportCutoff S.C s ≤ tAwakeEnd := C.tEnd M F
  have hvtσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hcσ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hσs
  have hcs1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ ≤ s by omega)
  have hsync := (C.syncStart M F U) hσ
  have hmx1 := le_max_left (Δ S) Δs
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ :=
    (C.supporter_saved M F R C.E U) hσ hσs v hv X hX
  obtain ⟨H₁, hH₁T, hv₁, W₁, hHW₁, hW₁T, hfl₁, -, hr₁⟩ :=
    (C.frame_st M F R U Fx) hσ hσs u huA vote hsend p b hb1 hb2 hp i hi hi₀ hpi hNoP hRootsR htRi
  -- `vote` names one block of `u`'s tree at its tick
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hsend
    exact x.lbl_tickStep ⟨i, hi⟩
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := C.E.not_mem_corrupted_of_tick hkU
  have hkUs : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
    have h := (C.E.tick_active _ u _ hkU).2.2
    have : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + Δ S ≤ M.supportCutoff S.C s by omega)
    linarith
  have hH : H₁ = H_u := by
    rw [hvote] at hv₁
    simp only [GoldfishVote.mk.injEq, true_and] at hv₁
    exact C.hRoots _ u _ hkU (by omega) H₁ H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (v := u) huk le_rfl hH₁T) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (v := u) huk le_rfl hHT) hv₁.symm
  rw [hH] at hHW₁
  have hYW := ancestorEq_trans hYX (ancestorEq_trans hXH hHW₁)
  -- `p` ticks to one delay after the vote time before `b`, so `W₁` is in its tree before `b`
  have hpA := (C.awakeHonest M F) R C.E p (t₁ := tGAT) (b := b) le_rfl (le_trans hb2 hcE) hp
  have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) := by
    exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C σ + Δ S by omega)
  have h2R : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) + Δ S ≤ (b : ℝ) := by
    exact_mod_cast (show M.voteTime S.C σ + Δ S + Δ S ≤ b by omega)
  have hkP := (tickStep_spec M) x R C.E (t := M.voteTime S.C σ + Δ S) (v := p) (by omega)
    (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hpA)
  have hkPb : x.tickStep p (M.voteTime S.C σ + Δ S) ≤ i := by
    refine le_trans ?_ hi₀
    by_contra hc
    have h := htime (show x.stepBefore (M.voteTime S.C σ + 2 * Δ S) + 1 ≤ x.tickStep p (M.voteTime S.C σ + Δ S) by omega)
    have hsb := ((stepBefore_time M) x R C.E (show 1 ≤ M.voteTime S.C σ + 2 * Δ S by omega)).2
    have h2R' : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + Δ S + Δ S ≤ M.voteTime S.C σ + 2 * Δ S by omega)
    linarith [hkP.2.2]
  have hW₁b : W₁ ∈ (x.st i p).tree := (mem_T_mono M F) x R C.E p hkPb hW₁T
  have hinv := (lem11_node_invariant M F S A x R C.E i p hpi).1
  rcases (compatible_iff _ _).1 hr₁ with hRW | hWR
  · have hFW := ancestorEq_trans
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R C.E i p) hRW
    refine ⟨W₁, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW₁b, hFW⟩, ?_, hYW⟩
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hinv]
    exact ⟨hW₁b, hFW, by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hRW, hfl₁⟩
  · obtain ⟨W', hW'⟩ := (frame_has_viable_head_st M F) S A x R C.E i p
    have hW'' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hinv _).1 hW'
    have hRW' := hW''.2.2.1
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hRW'
    exact ⟨W', ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hW''.1, hW''.2.1⟩, hW',
      ancestorEq_trans hYW (ancestorEq_trans hWR hRW')⟩

end B6CtxUpTo

/-- `WinCtx M S Sched x GST tGAT tAwakeEnd r m i rs s₀`: the hypotheses the window of the opening
`i` (first slot `s₀ + 1 = rs i * R ≤ r * R`) is read under: the execution assumptions and
unforgeability, every honest validator awake in the phase, fewer than a third in the adversary set,
committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m` with `i ≤ m`, and
no validator outside the adversary set with a `ForkChoiceChangeStep` at a step from the validator's own tick to the vote time of slot
`s₀ + 1 − k − 1` to before the support cutoff of slot `s₀ + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `s₀`: the slot before the honest round opening slot.

Roots name blocks until `M.supportCutoff S.C (s₀ + 1 + 1) + ΔClockBehind`: the latest real time of a tick a reader of
the bundle reads, the members' update at the action time of the opening's first slot (`base`).

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`, the members' update at the action time
of the opening's first slot; every reader of the bundle reads deliveries due by then.

Read aloud: the hypotheses under which the window of honest round opening slot `i` is read, with the
delivery premises up to the support cutoff of slot `s₀ + 2`. -/
structure WinCtxUpTo (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ) (s₀ : ℕ) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- Blocks and Goldfish votes due by the bound are delivered within `Δ` after `GST`. -/
  E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s₀ + 1 + 1))
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`, when that is at most the bound. -/
  Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject release ΔRedeliver Δs GST (M.supportCutoff S.C (s₀ + 1 + 1))
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  /-- Roots name blocks until the behind bound after the support cutoff of slot `s₀ + 2`: the real time of every tick
  to a clock value at most that cutoff (F-P1-35, `base`'s per-tick reads). -/
  hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + ΔClockBehind)
  hParent : ParentHeldAtDelivery M x
  hGST : GST ≤ tGAT
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  /-- At every slot of the phase, every validator honest at the slot's update is an honest active validator and an
  updater of the slot. -/
  hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
    ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
      v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s
  hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd
  hEnd : aR M S r ≤ tAwakeEnd
  hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd
  hi : i ≤ m
  hs : rs i * S.C.R = s₀ + 1
  hrR : s₀ + 1 ≤ r * S.C.R
  /-- No change at a step from a validator's own tick to the window's start value to before one of its own ticks
  to a clock value at most the support cutoff of slot `s₀ + 1`. -/
  hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1 - S.C.k - 1)) → k ≤ j →
    x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (s₀ + 1) → j < k' → w ∉ A.corrupted j →
    ¬ ForkChoiceChangeStep M S A x w j

namespace WinCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ : ℕ}

/-- The opening is at or after the first one.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: honest round opening slot `i`'s first slot is at least the first honest round opening
slot's. -/
theorem rs0 {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    rs 0 * S.C.R ≤ s₀ + 1 := by
  rw [← C.hs]
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact Nat.mul_le_mul_right _ (r_lt_of_lt_of_mono rs m C.hSeq.mono 0 i h C.hi).le

/-- Every window from the opening on starts after the committee premise's anchor.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle; `σ`: the last
  slot of the window.

Read aloud: every window ending at a slot from `s₀ + 1` on starts after the anchor of the committee
premise. -/
theorem win (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (h : s₀ + 1 ≤ σ) :
    2 * S.C.k ≤ σ ∧ anchorCW S tGAT ≤ M.slotStart S.C (σ - S.C.k - 1) := by
  have hw := (GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m tGAT tAwakeEnd σ C.hSeq (le_trans (C.rs0 M F) h)
  have h2 := hw.1
  have hk := S.C.k_ge_two
  exact ⟨h2, le_trans hw.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))⟩

/-- The support cutoff of the opening's first slot is at most `aR M S r`.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: the support cutoff of slot `s₀ + 1` is at most `aR M S r`. -/
theorem cut_le {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    M.supportCutoff S.C (s₀ + 1) ≤ aR M S r := by
  unfold aR
  have := C.hrR
  exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)

/-- No fork-choice change at `w` at a step from its own tick to the window's start clock value (the vote
time of slot `s₀ + 1 − k − 1`) to before `b`, inside the window.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `w`: the validator; `k`: the step of `w`'s tick to
  the window's start; `b`: the time.

Read aloud: `w` has no fork-choice change at a step from its tick to the window's start to before `b`,
inside the window. -/
theorem noChange (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V) {k k' c : ℕ}
    (hk : x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1 - S.C.k - 1)))
    (hk' : x.lbl k' = Event.tick w c) (hc : c ≤ M.supportCutoff S.C (s₀ + 1)) :
    ∀ j : ℕ, k ≤ j → j < k' → ¬ ForkChoiceChangeStep M S A x w j :=
  fun j hkj hjk => C.hNo w j k k' c hk hkj hk' hc hjk
    (E.not_mem_corrupted_of_le hjk.le ((Activity.mem_active.1 (E.tick_active k' w c hk').1).2))

/-- A validator honest at `b ≤ tAwakeEnd` is awake and honest at every time from `t₁ ≥ tGAT` to
`b`.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `w`: the validator; `t₁`, `b`: the times.

Read aloud: a validator honest at `b ≤ tAwakeEnd` is awake and honest at every time from `t₁ ≥ tGAT`
to `b`. -/
theorem awakeHonest (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V)
    {t₁ b : ℕ} (h1 : tGAT ≤ t₁) (hb : b ≤ tAwakeEnd) (hw : w ∉ A.corruptedAtTime x b) :
    w ∈ A.activeThroughout x t₁ b :=
  (mem_activeThroughout_of_hAwake_honest_at M F) R E C.hAwake h1 hb hw

/-- B6's context at the window ending at the opening's first slot.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle.

Read aloud: B6's bundle holds for the window ending at slot `s₀ + 1`. -/
theorem b6 (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    B6CtxUpTo M S A x GST tGAT tAwakeEnd r (s₀ + 1) Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet := by
  have hw := (C.win M F U) (le_refl (s₀ + 1))
  have hk2 := S.C.k_ge_two
  have hle : M.supportCutoff S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1 + 1) := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)
  have hBΔ : ΔClockBehind < Δ S := by linarith [C.hSkew, C.E.ahead_nonneg]
  have hB1 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) + ΔClockBehind ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
    have : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
    linarith
  have hrR := C.hrR
  have hR := S.C.R_ge_two
  have haR : M.supportCutoff S.C (s₀ + 1 + 1) ≤ aR M S r := by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  exact
    { E := GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy.restrict C.E fun _ _ _ h => by
        obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
        exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2
          ⟨le_trans h1 (by exact_mod_cast hle), rfl⟩, hNet := C.hNet, hSkew := C.hSkew, hRedeliver := C.hRedeliver, Sy := C.Sy.mono hle,
      hΔs := C.hΔs, hRoots := (per_tick_roots_of_roots_until M F) x C.E C.hRoots (le_trans hB1 (le_add_of_nonneg_right C.E.behind_nonneg)),
      hParent := C.hParent, hGST := C.hGST, hThird := C.hThird, hAwake := C.hAwake, hActive := C.hActive,
      hCommittees := C.hCommittees, hEnd := C.hEnd,
      hk := by have := hw.1; omega, hBefore := C.cut_le M F,
      hTick := (tick_time_le_of_clock_le M F) x C.E (le_trans hB1 (by exact_mod_cast le_trans haR C.hEnd)),
      hAnchor := le_trans hw.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)),
      hNo := C.hNo }

/-- The window before the opening is stable (B6, `stability_fact3`).

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle.

Read aloud: the window before slot `s₀ + 1` is stable. -/
theorem stable (R : RunFacts M S x) {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    FrontWindowStable M S A x (Hon M S A x) (s₀ + 1 - 2 * S.C.k) (s₀ + 1 - 1) := by
  by_contra hF
  have B := (C.b6 M F U)
  obtain ⟨w, j, k, k', c, h1', h1'', hk', hc, hjk, h3, h4⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.stability_fact3_upTo M F U Fx) S A x R GST tGAT
    tAwakeEnd r (s₀ + 1) B.E B.hNet B.hSkew B.hRedeliver B.Sy B.hΔs B.hRoots B.hParent B.hGST B.hThird B.hAwake
    B.hActive B.hCommittees B.hEnd B.hk B.hBefore B.hTick B.hAnchor hF
  exact B.hNo w j k k' c h1' h1'' hk' hc hjk h3 h4

/-- The front's bundle for the window before the opening (`FrontHyps` with `s_w := s₀ + 1 − 2k`,
`s' := s₀`, the member sets `Hon M S Sched`), with the end time the support cutoff of slot `s₀ + 1`.

Roots name blocks until `M.supportCutoff S.C s₀`: the bundle carries the premise at the support
cutoff of its slot `s' := s₀`.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle.

Read aloud: the front's bundle `FrontHyps` holds for the window before slot `s₀ + 1`. -/
theorem front (R : RunFacts M S x) {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    FrontHypsUpTo M S A x GST tGAT (M.supportCutoff S.C (s₀ + 1)) (s₀ + 1 - 2 * S.C.k) s₀
      (Hon M S A x) Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet := by
  have hw := (C.win M F U) (le_refl (s₀ + 1))
  have hk := S.C.k_ge_two
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (C.cut_le M F) C.hEnd
  have C6 := (C.b6 M F U)
  have hSt := (C.stable M F R U Fx)
  rw [Nat.add_sub_cancel] at hSt
  have hsc : M.supportCutoff S.C s₀ ≤ M.supportCutoff S.C (s₀ + 1 + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  refine ⟨C.E.mono hsc, C.hNet, C.hSkew, C.hRedeliver, C.Sy.mono hsc, C.hΔs,
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_trans (by exact_mod_cast ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) (le_add_of_nonneg_right C.E.behind_nonneg)) C.hRoots,
    (per_tick_roots_of_roots_until M F x C.E (c₀ := M.supportCutoff S.C (s₀)) C.hRoots (by
      have h := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ ≤ s₀ + 1 + 1 by omega)
      have h' : ((M.supportCutoff S.C (s₀) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
      linarith)), C.hParent, (votesCastByOwner_of_unforgeability M F S A x R C.E), C.hGST,
    ?_, ?_, ?_, (hAwake_shorter M F) R C.E C.hAwake hEs,
    fun s h1 h2 => C.hActive s h1 (le_trans h2 hEs), ?_, ?_, le_rfl, hSt.1⟩
  · -- `hGSTw`: the anchor is at or before the start of slot `s_w + 1`
    have hA := ((GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m tGAT
      tAwakeEnd (s₀ + 1) C.hSeq (C.rs0 M F)).2
    rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq, Nat.mul_add] at hA
    obtain ⟨-, -, hf, hs, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
      (s₀ + 1 - 2 * S.C.k)
    have hG := C.hGST
    have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
      have hA0 := C.E.ahead_nonneg
      have hB0 := C.E.behind_nonneg
      have h := C.hΔs
      have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
      exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
    rcases max_choice (Δ S) Δs with hmc | hmc <;> rw [hmc] <;> omega
  · intro s₁ h1 h2
    exact ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (s₁ + 1) (s₁ + 1 + 1) tAwakeEnd R C.E (Nat.le_succ _)
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEs)).1
  · intro s₁ _ _ v hv
    exact (Finset.mem_sdiff.1 hv).2
  · intro s₁ h1 h2
    exact (C6.members M F C6.E U R (σ := s₁) (by omega) (by omega)).2
  · have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1 - 2 * S.C.k)
      ((GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (s₀ + 1) C.hSeq (C.rs0 M F)).2
    omega

/-- **The members' windows.** For a slot `σ` from `s₀` to `s₀ + 1`, every member `w` of
`Hon M S Sched σ` is awake and honest at every time from the duty window's start of slot `σ + 1` to
the support cutoff of slot `σ + 1`.

Why: `w` is honest at that support cutoff, which is at most `aR M S r ≤ tAwakeEnd`; the duty window
of slot `σ + 1` starts after `tGAT` (the window ending at slot `s₀ + 1` starts after the anchor of
the committee premise, `win`); every validator honest in the phase is awake.

A helper of the recoveries of `fam` and `base`, whose record forms read the members' clauses at
the tick's outcomes, with no landed twin.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `C`: the context; `σ`: the slot.

Read aloud: the members of the slots `s₀` and `s₀ + 1` are awake and honest from the duty window's
start of the next slot to its support cutoff. -/
theorem honWindow (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ} (h1 : s₀ ≤ σ)
    (h2 : σ ≤ s₀ + 1) :
    ∀ w ∈ Hon M S A x σ, ∀ t : ℕ, M.dutyWindowStart S.C (σ + 1) ≤ t →
      t ≤ M.supportCutoff S.C (σ + 1) → w ∈ A.activeAtTime x t := by
  intro w hw t ht1 ht2
  have hk := S.C.k_ge_two
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hA : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1 + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (by omega))
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S
    tGAT (σ + 1) hA
  have hrR := C.hrR
  have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show σ + 1 ≤ r * S.C.R + 1 by omega)
  have hE : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd := le_trans hm C.hEnd
  exact Activity.mem_activeAtTime_of_mem_activeThroughout
    (C.awakeHonest M F R E w (t₁ := tGAT) le_rfl hE (Finset.mem_sdiff.1 hw).2) (by (norm_cast; omega)) (by exact_mod_cast ht2)

/-- **The window's family.** For the opening's proposer `p` (honest at the support cutoff of its
slot, `HonestOpeningSeq`) and its state before the start of slot `s₀ + 1`: the chain invariant and
the lock invariant hold at slot `s₀` at `Hon M S Sched s₀` for `WinFam M S Sched x s₀`; the family
holds `p`'s anchor and every member's root before the vote time of slot `s₀ + 1`; and `p`'s frame
has, for every block of the family, a viable head that is that block or a descendant of it.

Why: the window is stable (B6). The front's chain step (`front_step_family`) gives the chain
invariant for the live locks of slot `s₀ − 1` and the confirmations of slot `s₀ − 1`, and
`front_of_frontWindowStable` for `FrontFamily`, with its lock invariant; ancestors inherit both.
The anchor is `p`'s root, an ancestor of `p`'s own confirmation of slot `s₀ − 1`
(`B6Ctx.rootChain_at`), or a locked block,
on `p`'s confirmation of slot `s₀ − 1` or a live lock before the vote time of slot `s₀`
(`live_lock_entry_source`). A block of the family is on the chain of a member's confirmation of a
window slot (a lock is made on one, `lock_entry_confirmation`; a member's root is on one, the
window's second clause), whose honest supporter's vote gives `p` a viable head on its chain
(`B6Ctx.frameP_of_conf`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

Read aloud: the window's family satisfies the chain and lock invariants at slot `s₀`, holds the
proposer's anchor and every member's root, and each of its blocks has a viable head of the proposer
on its chain. -/
theorem fam (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    ChainInvFor M S A x (Hon M S A x s₀) (WinFam M S A x s₀) s₀ ∧
    (∀ w ∈ Hon M S A x s₀, LiveLocksOnFamilyAt M S A x (WinFam M S A x s₀) s₀ w) ∧
    WinFam M S A x s₀
      (M.get_anchor (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)))
      ((M.slotStart S.C (s₀ + 1) : ℕ) : Int)) ∧
    (∀ w ∈ Hon M S A x s₀,
      WinFam M S A x s₀ (M.get_fc_root (x.tickInput w (M.voteTime S.C (s₀ + 1))))) ∧
    (∀ D : Block V, WinFam M S A x s₀ D →
      ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)))).tree,
        W ∈
          (M.fg_to_ac
              (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
        D.AncestorEq W) := by
  -- F-P1-14: the `dev` body at tick inputs (rule R3): the proposer's frame read at its tick to the start of slot
  -- `s₀ + 1` (`frameP_of_conf_st`), the anchor's lock through `live_lock_entry_source` at that tick
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (C.cut_le M F) C.hEnd
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀ + 1 ≤ s₀ + 1 + 1 by omega)
  have hμ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 - S.C.k - 1)
  have hμs := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ - 1 by omega)
  have hss0 : M.slotStart S.C s₀ = M.slotStart S.C (s₀ - 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ - 1), ← Nat.mul_add_one]
    congr 1
    omega
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest M F R C.E p (t₁ := tGAT) le_rfl hEs hpH
  have H := (C.front M F R U Fx)
  have C6 := (C.b6 M F U)
  have hSt := (C.stable M F R U Fx)
  rw [Nat.add_sub_cancel] at hSt
  have hstep := (GoldilocksCorrectness.Record.Proofs.Executions.front_step_family_upTo M F U R) H (s₀ - 1) (by omega) (by omega)
  have hext : ∀ D : Block V, (liveLockAncestors M S A x (Hon M S A x (s₀ - 1)) (s₀ - 1) D ∨
      ∃ v ∈ Hon M S A x (s₀ - 1 + 1), ∃ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s₀ - 1 + 1))).savedConfirmation (s₀ - 1) =
          some C' ∧ D.AncestorEq C') →
      HonestChainExtends M S A x (Hon M S A x s₀) D s₀ := by
    intro D hD
    have h := hstep D hD
    rwa [show s₀ - 1 + 1 = s₀ by omega] at h
  obtain ⟨hFF, hFL⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.front_of_frontWindowStable_upTo M F U) S A x R GST tGAT tAwakeEnd (s₀ + 1) (Hon M S A x)
    (C.E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) C.hNet C.hSkew C.hRedeliver (C.Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) C.hΔs
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_trans (by exact_mod_cast ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₀ + 1 - 1 ≤ s₀ + 1 + 1 by omega))) (le_add_of_nonneg_right C.E.behind_nonneg)) C.hRoots)
    (per_tick_roots_of_roots_until M F x C.E (c₀ := M.supportCutoff S.C (s₀ + 1 - 1)) C.hRoots (by
      have h := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ + 1 - 1 ≤ s₀ + 1 + 1 by omega)
      have h' : ((M.supportCutoff S.C (s₀ + 1 - 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
      linarith))
    C.hParent (votesCastByOwner_of_unforgeability M F S A x R E) C.hGST H.hGSTw hw0.1
    H.hHonMono H.hHon C.hAwake C.hActive
    H.hCommittees H.hsw (by rw [Nat.add_sub_cancel]; exact hEs)
    (by rw [Nat.add_sub_cancel]; exact (C.stable M F R U Fx))
  rw [Nat.add_sub_cancel] at hFF hFL
  have hmem : ∀ a b : ℕ, a ≤ b → b ≤ s₀ + 1 → ∀ u ∈ roundMembers M S A x b,
      u ∈ roundMembers M S A x a := fun a b hab hb u hu =>
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A a b tAwakeEnd R E hab
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hb) hEs)).1 hu
  have hpHon : ∀ a : ℕ, a ≤ s₀ + 1 → p ∈ roundMembers M S A x a := fun a ha =>
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S ha) hpH⟩
  -- `p`'s tick to the start of slot `s₀ + 1`, the step its frame is read at
  set kp := x.tickStep p (M.slotStart S.C (s₀ + 1)) with hkpdef
  have hss1 : M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) := by omega
  have hkP := (tickStep_spec M) x R E (t := M.slotStart S.C (s₀ + 1)) (v := p) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show tGAT + Δ S ≤ M.slotStart S.C (s₀ + 1) by omega)
          linarith)
      (by have : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
            exact_mod_cast hss1
          linarith) hpAH)
  have hkpl : x.lbl kp = Event.tick p (M.slotStart S.C (s₀ + 1)) := hkP.1
  have hpkp : p ∉ A.corrupted kp := E.not_mem_corrupted_of_tick hkpl
  have hkpT : x.time kp ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) :=
    (tick_time_le_of_clock_le M F) x E (c₀ := M.slotStart S.C (s₀ + 1))
      (by have : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
          linarith) kp p _ hkpl le_rfl
  have hkpE : x.time kp ≤ (tAwakeEnd : ℝ) :=
    (tick_time_le_of_clock_le M F) x E (c₀ := M.slotStart S.C (s₀ + 1))
      (by have : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ tAwakeEnd by omega)
          linarith) kp p _ hkpl le_rfl
  -- `p`'s tick to the window's start value
  have hk0 : x.lbl (x.tickStep p (M.voteTime S.C (s₀ + 1 - S.C.k - 1))) =
      Event.tick p (M.voteTime S.C (s₀ + 1 - S.C.k - 1)) := by
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1 - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
    exact ((tickStep_spec M) x R E (t := M.voteTime S.C (s₀ + 1 - S.C.k - 1)) (v := p) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hpAH)).1
  -- the frame of `p` on the chain of a member's confirmation
  have hFrameConf : ∀ (σ : ℕ) (v : V) (X Y : Block V), s₀ + 1 - S.C.k - 1 ≤ σ →
      σ + 2 ≤ s₀ + 1 → v ∈ roundMembers M S A x (σ + 1) →
      (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X →
      Y.AncestorEq X →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
          Y.AncestorEq W := by
    intro σ v X Y h1 h2 hv hX hYX
    have hvσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
    have hsσ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show σ + 2 ≤ s₀ + 1 from h2)
    have hss' : M.slotStart S.C (σ + 2) = M.slotStart S.C σ + 8 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ, Nat.mul_add]
      omega
    have hμσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S h1
    have hb2 : M.voteTime S.C σ + 2 * Δ S ≤ M.supportCutoff S.C (s₀ + 1) := by omega
    have hp := (not_mem_corruptedAtTime_of_le M) x R E hb2 hpH
    have hkpb : ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) ≤ x.time kp := by
      have : ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C σ + 2 * Δ S + Δ S ≤ M.slotStart S.C (s₀ + 1) by omega)
      linarith [hkP.2.1]
    have hi₀ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ kp :=
      ((stepBefore_lt_of_le_time M) x R E (by omega) hkpb).le
    have hk0b : x.tickStep p (M.voteTime S.C (s₀ + 1 - S.C.k - 1)) < x.stepBefore (M.voteTime S.C σ + 2 * Δ S) := by
      refine (lt_stepBefore_of_not_other M) x R E (by rw [hk0]; simp) ?_
      have h := (E.tick_active _ p _ hk0).2.2
      have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S ≤ M.voteTime S.C σ + 2 * Δ S by omega)
      linarith
    exact C6.frameP_of_conf_st M F R U Fx (σ := σ) h1 h2 v hv X Y hX hYX p
      (M.voteTime S.C σ + 2 * Δ S) le_rfl hb2 hp kp hkpE hi₀ hpkp
      (fun j hj hjk => C6.noChange M F R C.E p hk0 hkpl (by omega) j (by omega) hjk) C.hRoots
      (le_trans hkpT (le_add_of_nonneg_right C.E.behind_nonneg))
  -- the frame of `p` on the chain of a live lock at a clock value `t` from the vote time of slot `s₀`
  -- to the start of slot `s₀ + 1`
  have hFrameLock : ∀ (t : ℕ) (u : V) (e : M.LE) (Y : Block V),
      M.voteTime S.C s₀ ≤ t → t ≤ M.slotStart S.C (s₀ + 1) → u ∈ roundMembers M S A x s₀ →
      e ∈ (x.tickInput u t).lockEntries → ((t : ℕ) : Int) < e.d → Y.AncestorEq e.B →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
          Y.AncestorEq W := by
    intro t u e Y ht1 ht2 hu he hlive hYe
    obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.lock_entry_confirmation M F U) S A x R t u e E he
    have hσlo : s₀ - S.C.k ≤ σ :=
      (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
        (s₀ - S.C.k) σ t e hd hlive (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (by omega)) ht1)
    have hσhi : σ + 2 ≤ s₀ + 1 := by
      by_contra h
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 ≤ σ + 1 by omega)
      have h2' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
      have h3' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
      omega
    have huσ : u ∈ roundMembers M S A x (σ + 1) :=
      hmem (σ + 1) s₀ (by omega) (by omega) u hu
    exact hFrameConf σ u C' Y (by omega) hσhi huσ hsv (ancestorEq_trans hYe heC')
  -- the frame of `p` on the chain of every block of the hstep family and of `FrontFamily`
  have hFrameDom : ∀ D : Block V, (liveLockAncestors M S A x (Hon M S A x (s₀ - 1)) (s₀ - 1) D ∨
      (∃ v ∈ Hon M S A x (s₀ - 1 + 1), ∃ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s₀ - 1 + 1))).savedConfirmation (s₀ - 1) =
          some C' ∧ D.AncestorEq C') ∨
      FrontFamily M S A x (Hon M S A x s₀) s₀ D) →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
          D.AncestorEq W := by
    intro D hD
    rcases hD with ⟨u, hu, e, he, hl, hDe⟩ | ⟨v, hv, C', hC', hDC'⟩ | hF
    · have hl' := hl
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
      rw [show s₀ - 1 + 1 = s₀ by omega] at he hl'
      have hu' : u ∈ roundMembers M S A x s₀ := by
        have h := hu
        simp only [Hon] at h
        rwa [show s₀ - 1 + 1 = s₀ by omega] at h
      exact hFrameLock (M.voteTime S.C s₀) u e D le_rfl (by omega) hu' he hl'.1 hDe
    · rw [show s₀ - 1 + 1 = s₀ by omega] at hv hC'
      exact hFrameConf (s₀ - 1) v C' D (by omega) (by omega)
        (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hmem s₀ (s₀ + 1) (by omega) le_rfl v hv)
        (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hC') hDC'
    · rcases hF with ⟨u, hu, e, he, hl, rfl⟩ | ⟨w', hw', rfl⟩
      · have hl' := hl
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
        obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.lock_entry_confirmation M F U) S A x R _ u e E he
        have hσlo : s₀ + 1 - S.C.k ≤ σ :=
          (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
            (s₀ + 1 - S.C.k) σ (M.voteTime S.C (s₀ + 1)) e hd hl'.1 ((GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (by omega))
        have hσhi : σ + 2 ≤ s₀ + 1 := by
          by_contra h
          have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 ≤ σ + 1 by omega)
          have h2' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
          have h3' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
          omega
        exact hFrameConf σ u C' e.B (by omega) hσhi (hmem (σ + 1) (s₀ + 1) (by omega) le_rfl u hu)
          hsv heC'
      · obtain ⟨D, hDc, hRD⟩ := hSt.2 w' hw'
        rcases hDc with ⟨u, hu, e, he, hl, rfl⟩ | ⟨v, hv, hconf⟩
        · have hl' := hl
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
          obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.lock_entry_confirmation M F U) S A x R _ u e E he
          have hσlo : s₀ + 1 - S.C.k ≤ σ :=
            (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
              (s₀ + 1 - S.C.k) σ (M.voteTime S.C (s₀ + 1)) e hd hl'.1 ((GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (by omega))
          have hσhi : σ + 2 ≤ s₀ + 1 := by
            by_contra h
            have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 ≤ σ + 1 by omega)
            have h2' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
            have h3' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
            omega
          exact hFrameConf σ u C' _ (by omega) hσhi
            (hmem (σ + 1) (s₀ + 1) (by omega) le_rfl u hu) hsv (ancestorEq_trans hRD heC')
        · exact hFrameConf (s₀ - 1) v D _ (by omega) (by omega)
            (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hmem s₀ (s₀ + 1) (by omega) le_rfl v hv)
            (by rw [show s₀ - 1 + 1 = s₀ by omega]; exact hconf) hRD
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the chain invariant
    rintro D ⟨D', hD', hDD'⟩
    refine (GoldilocksCorrectness.Record.Proofs.Executions.honestChainExtends_of_ancestorEq M F) S A x _ D' D s₀ hDD' ?_
    rcases hD' with h | h | h
    · exact hext D' (Or.inl h)
    · exact hext D' (Or.inr h)
    · exact hFF D' h
  · -- the lock invariant
    intro w hw n' sent hR hAw e he hl
    obtain ⟨D, hD, heD⟩ := hFL w hw n' sent hR hAw e he hl
    exact ⟨D, ⟨D, Or.inr (Or.inr hD), ancestorEq_refl D⟩, heD⟩
  · -- the anchor
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_cases_locked M F) (x.tickInput p (M.slotStart S.C (s₀ + 1)))
      ((M.slotStart S.C (s₀ + 1) : ℕ) : Int) with ha | ⟨hVT, e, he, hl, hAe⟩
    · rw [ha]
      have hp' : p ∈ Hon M S A x (s₀ - 1 + 1) := by
        rw [show s₀ - 1 + 1 = s₀ by omega]
        exact hpHon (s₀ + 1) le_rfl
      obtain ⟨D, hD, hRD⟩ := C6.rootChain_at M F R U Fx (σ := s₀ - 1) (by omega) p hp'
        (M.slotStart S.C (s₀ + 1)) (by rw [show s₀ - 1 + 1 = s₀ by omega]; omega)
        (by rw [show s₀ - 1 + 2 = s₀ + 1 by omega]; omega)
      exact ⟨D, Or.inr (Or.inl ⟨p, hp', D, hD, ancestorEq_refl D⟩),
        by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hRD⟩
    · have hl' := hl
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
      have hdwS : M.dutyWindowStart S.C (s₀ - 1 + 2) ≤ M.slotStart S.C (s₀ + 1) := by
        rw [show s₀ - 1 + 2 = s₀ + 1 by omega]
        exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s₀)
          ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
      have hdwG : tGAT + Δ S ≤ M.dutyWindowStart S.C (s₀ - 1 + 2) := by
        rw [show s₀ - 1 + 2 = s₀ + 1 by omega]
        have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1)
          (le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
        omega
      have hpTT : p ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s₀ - 1 + 2) : ℕ) : ℤ) (M.slotStart S.C (s₀ + 1)) := by
        refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega) (by exact_mod_cast hdwS) ?_
        refine Activity.mem_activeThroughout_of_le ?_ ?_ hpAH
        · have h : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (s₀ - 1 + 2) : ℕ) : ℝ) := by exact_mod_cast hdwG
          push_cast
          linarith
        · have h : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
            exact_mod_cast hss1
          linarith
      rcases (live_lock_entry_source M F U) S A x R (s₀ - 1) (M.slotStart S.C (s₀ + 1)) p E C.hSkew hpTT
          (by rw [show s₀ - 1 + 1 = s₀ by omega]; omega)
          (by rw [show s₀ - 1 + 2 = s₀ + 1 by omega]; omega) e he hl'.1 with
        ⟨C', hC', heC'⟩ | ⟨n₃, sent₃, hrun₃, hA₃, e', he', hl₃, hee'⟩
      · exact ⟨e.B, Or.inr (Or.inl ⟨p, hpHon _ (by omega), C', hC', heC'⟩), hAe⟩
      · obtain ⟨e₁, he₁, hl₁, -, he'₁, -⟩ :=
          GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
            (Nat.le_add_left 1 (s₀ - 1))
            ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ - 1 + 1) p n₃ sent₃ hrun₃ hA₃) e' he'
        exact ⟨e₁.B, Or.inl ⟨p, hpHon _ (by omega), e₁, he₁, hl₁,
          ancestorEq_refl _⟩, ancestorEq_trans hAe (ancestorEq_trans hee' he'₁)⟩
  · -- the members' roots
    intro w hw
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩)), ancestorEq_refl _⟩
  · -- the proposer's frame
    rintro D ⟨D', hD', hDD'⟩
    obtain ⟨W, hWt, hWv, hD'W⟩ := hFrameDom D' hD'
    exact ⟨W, hWt, hWv, ancestorEq_trans hDD' hD'W⟩

/-- **The window's family is on the chain of the proposal's parent.** Every block of
`WinFam M S Sched x s₀` is `B.parent` or an ancestor of it, for the opening's proposal `B`
(`family_ancestorEq_proposal_parent`, with the honest committee votes of slot `s₀` and `fam`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

Read aloud: every block of the window's family is the proposal's parent or an ancestor of it. -/
theorem fam_parent (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∀ D : Block V, WinFam M S A x s₀ D → D.AncestorEq B.parent := by
  -- F-P1-14: the `dev` body; the proposer's pool read at its tick input (`counting_of_committee_majority_st`)
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (C.cut_le M F) C.hEnd
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hμs := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest M F R C.E p (t₁ := tGAT) le_rfl hEs hpH
  have hsy := (C.b6 M F U).syncStart M F U (σ := s₀) (by omega)
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hΔs := C.hΔs
  -- the members' sync window starts after `tGAT` and ends by the support cutoff of slot `s₀ + 1`
  have hΔsN : Δs < 4 * Δ S * S.C.k := by
    have h1 : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
    have h0 : (0 : ℝ) ≤ (Δ S : ℝ) := by positivity
    have h2 : (Δs : ℝ) < 4 * Δ S * S.C.k := by linarith
    exact_mod_cast h2
  have hHold0 : tGAT ≤ M.supportCutoff S.C s₀ - max (2 * Δ S) Δs := by
    have := Nat.mul_le_mul_left (4 * Δ S) (show S.C.k ≤ S.C.k + 2 by omega)
    omega
  have hHold1 : M.supportCutoff S.C s₀ - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C (s₀ + 1) := by omega
  have hpA : p ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (s₀ + 1)) :=
    (mem_activeThroughout_of_hAwake_honest_at M F) R C.E C.hAwake le_rfl hEs hpH
  -- `p`'s tick to the support cutoff of slot `s₀`
  have hc01R : ((M.supportCutoff S.C s₀ : ℕ) : ℝ) + ΔClockBehind ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C s₀ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C s₀ + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
    linarith
  have hG0 : ((tGAT : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) - ΔClockAhead := by
    have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.supportCutoff S.C s₀ by omega)
    linarith
  obtain ⟨kR, hkR, hkR1, hkR2⟩ := C.E.tick_of_active (M.supportCutoff S.C s₀) (by omega) p
    (fun j h1 h2 => Activity.mem_activeThroughout.1 hpA j (le_trans h2 hc01R)
      (le_trans (le_trans hG0 h1) (htime (Nat.le_succ j))))
  have hRootsP : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C s₀))) := by
    rw [(tickStep_eq_of_lbl M) x C.E hkR]
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ C.hRoots
    have : ((M.supportCutoff S.C s₀ : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ ≤ s₀ + 1 + 1 by omega))
    linarith
  -- `p`'s tick to the start of slot `s₀ + 1`, before the support cutoff of that slot
  obtain ⟨iB, hlB, hsB⟩ := hB
  have hTB : x.time iB ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
    have h1 := (C.E.tick_active iB p _ hlB).2.2
    have : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
    linarith
  have H := (C.front M F R U Fx)
  have hVot := H.voters M F R C.E U s₀ (by omega) le_rfl
  have hMaj := ((C.b6 M F U).members M F C.E U R (σ := s₀) (by omega) (by omega)).2
  obtain ⟨hChain, -, hAnchor, -, hFrameP⟩ := (C.fam M F R E U Fx)
  exact (GoldilocksCorrectness.Record.Proofs.Executions.family_ancestorEq_proposal_parent_upTo M F U) S A x R GST s₀ (S.P.committee s₀ ∩ Hon M S A x s₀)
    (WinFam M S A x s₀) B p (C.E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) C.hNet C.hSkew C.hRedeliver (C.Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) C.hΔs
    hRootsP C.hParent (votesCastByOwner_of_unforgeability M F S A x R E)
    (by omega)
    (fun u hu => by
      obtain ⟨huH, hK, vote, -, -, i', hl', hs'⟩ := hVot u hu
      refine ⟨hK, ?_, vote, i', hl', hs'⟩
      rw [(tickStep_eq_of_lbl M) x C.E hlB]
      exact (not_mem_corrupted_of_le_time M) x R C.E (Finset.mem_sdiff.1 huH).2 hTB)
    (fun D hD u hu vote hs => (hChain D hD).1 u (Finset.mem_inter.1 hu).2 vote hs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R E s₀ (x.tickStep p (M.slotStart S.C (s₀ + 1))) (Hon M S A x s₀) p
      hMaj).2.1
    (fun u hu => by
      have hub : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) :=
        (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2
      refine Activity.mem_activeThroughout_of_le ?_ ?_
        ((mem_activeThroughout_of_hAwake_honest_at M F) R C.E C.hAwake le_rfl hEs hub)
      · exact_mod_cast hHold0
      · have : ((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) ≤
            ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hHold1
        push_cast at this
        exact this)
    ⟨kR, hkR, fun j h1 h2 => Activity.mem_activeThroughout.1 hpA j
      (le_trans (htime h2) (le_trans hkR2 hc01R))
      (le_trans (le_trans (by exact_mod_cast hHold0) h1) (htime (Nat.le_succ j)))⟩
    ⟨iB, hlB, hsB⟩ hFrameP hAnchor

/-- **The round's first clause, read on the window.** Before the vote time of the opening's first
slot `s₀ + 1`, every member `w` of `Hon M S Sched (s₀ + 1)` has its root `B.parent` or an ancestor
of it (its root is in the window's family, `fam_parent`), and its `head_height_floor` at most
`B.parent`'s height (`B.parent` is a viable head of the proposer, `floor_le_of_viable_tick_upTo`, and
`head_height_floor` (the least chain-state height a viable block may have) does not rise until the vote time).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

Read at each member's tick input to the vote time.

Read aloud: in the state its tick to the vote time of slot `s₀ + 1` starts from, every member's root
is `B.parent` or an ancestor of it, with `head_height_floor` at most `B.parent`'s chain-state
height. -/
theorem clause1 (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∀ w ∈ Hon M S A x (s₀ + 1),
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (s₀ + 1)))).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ≤
        (M.chainStateOf S.C B.parent).h := by
  -- F-P1-22: the root part from `fam` and `fam_parent`; the floor part per tick: no change at `w` from its last
  -- step before `t := slotStart (s₀ + 1) − 2Δ` to its tick to the vote time (`C.noChange`), and `w`'s
  -- `head_height_floor` before `t` at most the proposer's at its tick to the slot start, where `B.parent` is a
  -- viable head (`floor_le_of_viable_tick_upTo`)
  intro w hw
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hrR := C.hrR
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (C.cut_le M F) C.hEnd
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd := by
    refine le_trans ?_ C.hEnd
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hws₀ : w ∈ Hon M S A x s₀ :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (s₀ + 1) (s₀ + 1 + 1) tAwakeEnd R E
      (Nat.le_succ _) hEs2).1 hw
  obtain ⟨-, -, -, hRoot, -⟩ := C.fam M F R E U Fx
  refine ⟨C.fam_parent M F R E U Fx B hB _ (hRoot w hws₀), ?_⟩
  -- the schedule's times, in natural numbers
  obtain ⟨hv1, hc1, -, -, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc2 := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)).2.1
  have hs2 := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)).2.2.2.1
  have hv0 := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
    (s₀ + 1 - S.C.k - 1)).1
  have hss0 : M.slotStart S.C (s₀ + 1 - S.C.k - 1) + 4 * Δ S * (S.C.k + 1) = M.slotStart S.C (s₀ + 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), ← Nat.mul_add]
    congr 1
    have := hw0.1
    omega
  have h12 : 4 * Δ S * 3 ≤ 4 * Δ S * (S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hanc := hw0.2
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hanc
  have hk2 : 4 * Δ S * S.C.k ≤ 4 * Δ S * (S.C.k + 2) := Nat.mul_le_mul_left _ (by omega)
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hSk := C.hSkew
  have hmx : max (Δ S) Δs < 4 * Δ S * S.C.k := by
    have h := C.hΔs
    have : ((max (Δ S) Δs : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast at h ⊢
      linarith
    exact_mod_cast this
  have hGSTt := C.hGST
  set t : ℕ := M.slotStart S.C (s₀ + 1) - 2 * Δ S with ht
  have htD : t + Δ S + Δ S = M.slotStart S.C (s₀ + 1) := by omega
  have hGt : GST + max (Δ S) Δs ≤ t + Δ S := by omega
  have hTt : tGAT + max (Δ S) Δs ≤ t + Δ S := by omega
  -- `w` is active from `tGAT` to the support cutoff of slot `s₀ + 2`; it ticks to the window's start value and to
  -- the vote time of slot `s₀ + 1`
  have hwH : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) := (Finset.mem_sdiff.1 hw).2
  have hwA := C.awakeHonest M F R E w (t₁ := tGAT) le_rfl hEs2 hwH
  have hc0a : tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1 - S.C.k - 1) := by omega
  have hc0b : M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S ≤ t := by omega
  obtain ⟨k0, hk0l, -, hk0t⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hwA
    (t := M.voteTime S.C (s₀ + 1 - S.C.k - 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) := by exact_mod_cast hc0a
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by omega)
  obtain ⟨kw, hkwl, hkwt, -⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hwA
    (t := M.voteTime S.C (s₀ + 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by omega)
  have hTw : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st kw w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkwl]
  -- the no-change window from the last step before `t` to `w`'s tick to the vote time
  have hk0sb : k0 ≤ x.stepBefore t := by
    refine ((time_lt_iff_le_stepBefore M) x R E (by omega)).1 ?_
    have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) := by exact_mod_cast hc0b
    push_cast at this; linarith
  have hsbkw : x.stepBefore t ≤ kw := by
    refine (stepBefore_le_of_le_time_st M F) R E ?_
    have : ((t + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
    push_cast at this; linarith
  have hfl1 := (floor_le_of_no_change_st M F) S A x R E w hsbkw
    (fun j h1 h2 => C.noChange M F R E w hk0l hkwl (by omega) j (le_trans hk0sb h1) h2)
  -- the proposer's tick to the start of slot `s₀ + 1`, at which `B.parent` is a viable head
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpA := C.awakeHonest M F R E p (t₁ := tGAT) le_rfl hEs hpH
  obtain ⟨kp, hlp, hsp⟩ := id hB
  obtain ⟨-, hkp1, hkp2⟩ := E.tick_active kp p _ hlp
  have hTp : x.tickInput p (M.slotStart S.C (s₀ + 1)) = x.st kp p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hlp]
  have hPV := (proposal_parent_viable_head M F U) S A x R E s₀ B p ⟨kp, hlp, hsp⟩
  rw [hTp] at hPV
  have hkpc : x.time kp ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
    have : ((M.slotStart S.C (s₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show _ ≤ _ by omega)
    push_cast at this; linarith
  have hkpc2 : x.time kp ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) :=
    le_trans hkpc (by exact_mod_cast (show _ ≤ _ by omega))
  -- F-P1-26-2: `p` read at its tick `kp` (`floor_le_of_viable_tick_upTo`), the window from `a := t + Δ S − max (Δ S) Δs`, and
  -- `p`'s earlier tick to the start of slot `s₀`
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hwt : w ∉ A.corruptedAtTime x t :=
    (not_mem_corruptedAtTime_of_le M) x R E (show t ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega) hwH
  have hsl : ∀ t' : ℕ, M.slot S.C t' = S.C.slot (t' : Int) := fun t' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslotw : ∀ Y ∈ (x.stateBefore t w).tree, M.slotStart S.C Y.slot ≤ M.slotStart S.C s₀ := by
    intro Y hY
    have hi := (time_stepBefore_le M) x R E t
    have hvS : w ∉ A.corrupted (x.stepBefore t) :=
      (not_mem_corrupted_of_le_time M) x R E hwt (by exact_mod_cast hi)
    have h := (slot_le_clockValue_of_mem_tree M F) R E hvS hY
    have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore t) w
    have hcvR : (x.clockValue (x.stepBefore t) w : ℝ) < ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
      have h1 : ((t + Δ S + Δ S : ℕ) : ℝ) = ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast htD
      have h2 : (1 : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ M.slotStart S.C (s₀ + 1) by omega)
      push_cast at h1
      refine lt_of_le_of_lt hcv (max_lt (by linarith) ?_)
      linarith
    have hlt := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout F.sched) S
      (Nat.cast_lt.1 hcvR)
    rw [hsl] at hlt
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (Nat.lt_succ_iff.mp (h.trans_lt hlt))
  have hA0' : tGAT + Δ S ≤ M.slotStart S.C s₀ := by omega
  obtain ⟨hk₂, -, -⟩ := (tickStep_spec M) x R E (t := M.slotStart S.C s₀) (v := p) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by
        have h1 : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hA0'
        push_cast at h1 ⊢; linarith)
      (by
        have h1 : ((M.slotStart S.C s₀ + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C s₀ + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
        push_cast at h1 ⊢; linarith)
      hpA)
  have hwin : ∀ i : ℕ, ((t + Δ S - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kp → p ∈ A.active i := by
    intro i h1 h2
    have h0 : ((tGAT : ℕ) : ℝ) ≤ ((t + Δ S - max (Δ S) Δs : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT ≤ t + Δ S - max (Δ S) Δs by omega)
    exact Activity.mem_activeThroughout.1 hpA i (le_trans (R.time_mono h2) hkpc)
      (le_trans h0 (le_trans h1 (R.time_mono (Nat.le_succ i))))
  have hfl3 := (floor_le_of_viable_tick_upTo M F U Fx) S A x R GST t (t + Δ S - max (Δ S) Δs) (M.slotStart S.C (s₀ + 1))
    (M.slotStart S.C s₀) kp (x.tickStep p (M.slotStart S.C s₀)) w p B.parent C.E C.hNet C.hSkew C.hRedeliver C.Sy
    C.hRoots C.hParent (C.hThird.mono (le_trans hkpc (by exact_mod_cast hEs))) (by omega) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by exact_mod_cast (show tGAT ≤ t + Δ S - max (Δ S) Δs by omega))
      (by exact_mod_cast (show t + Δ S - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)) hwA)
    hwt hlp (by omega) hwin hk₂ (by omega) hslotw hPV (le_trans hkpc2 (le_add_of_nonneg_right C.E.behind_nonneg))
    (show M.slotStart S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
  rw [hTw]
  exact le_trans hfl1 hfl3

end WinCtxUpTo

namespace WinCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ : ℕ}

/-- **The proposer's `head_height_floor` at its proposal is at most each member's at the vote time** (`base`'s row
`hFloorW`, read at the two ticks, rule R3; F-P1-28). For the opening's proposal `B`: the proposer's
`head_height_floor` on the state its tick to the start of slot `s₀ + 1` starts from is at most that of every member of
`Hon M S A x (s₀ + 1)` on the state its tick to the vote time of slot `s₀ + 1` starts from.

Why: the proposer has no fork-choice change from its last step before `t := slotStart (s₀ + 1) − Δ` to its tick
(`C.noChange`, `floor_le_of_no_change_st`), and its `head_height_floor` before `t` is at most the member's at its tick,
one delay later (`floor_le_of_delivery_tick_upTo`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal.

Read aloud: the proposer's `head_height_floor` when it proposes is at most every member's when it votes. -/
theorem floor_le_member_tick (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∀ w ∈ Hon M S A x (s₀ + 1),
      M.head_height_floor (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) := by
  -- F-P1-28: `round_base_steps` at `s := s₀ + 1`, each row read at the reader's own tick (rule R3); the rows of the
  -- members' windows as `round89r` supplies them (`hMemWin`, `hMemRd`, `hMemAct`),'s `tStart := tGAT + Δ S`
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (C.cut_le M F) C.hEnd
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (by unfold aR; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by have := C.hrR; omega)) C.hEnd
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss1 : M.slotStart S.C (s₀ + 1 + 1) = M.slotStart S.C (s₀ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hvf1 := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hcm01 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ s₀)
  have hcm12 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ (s₀ + 1))
  have htl1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1)
  have htl2 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1 + 1)
  have hμs := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hvμ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 - S.C.k - 1)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hsk := C.hSkew
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h := C.hΔs
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hk2 : 4 * Δ S * S.C.k ≤ 4 * Δ S * (S.C.k + 2) := Nat.mul_le_mul_left _ (by omega)
  have hcut : tGAT + 4 * Δ S * (S.C.k + 2) + 2 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
  have hm2 : tGAT + max (2 * Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
    rcases max_choice (2 * Δ S) Δs with h | h <;> rw [h] <;> omega
  have hm1 : tGAT + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpA := C.awakeHonest M F R C.E p (t₁ := tGAT) le_rfl hEs hpH
  obtain ⟨kp, hlp, hsp⟩ := id hB
  obtain ⟨-, hkp1, hkp2⟩ := C.E.tick_active kp p _ hlp
  have hTp : x.tickInput p (M.slotStart S.C (s₀ + 1)) = x.st kp p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x C.E hlp]
  -- the members of slot `s₀ + 1`: honest at the support cutoff of slot `s₀ + 2`, active from `tGAT` to it
  have hwH : ∀ w ∈ Hon M S A x (s₀ + 1), w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    fun w hw => (Finset.mem_sdiff.1 hw).2
  have hwA : ∀ w ∈ Hon M S A x (s₀ + 1), w ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    fun w hw => C.awakeHonest M F R C.E w (t₁ := tGAT) le_rfl hEs2 (hwH w hw)
  have hA2 : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1 + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hA1 : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hdw1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1) hA2
  have hAct : ∀ v ∈ Hon M S A x (s₀ + 1), v ∈ honestActiveAt M S A x (s₀ + 1) ∧ v ∈ updaterAt M S A x (s₀ + 1) :=
    fun v hv => C.hActive (s₀ + 1) (by omega) hEs2 v (hwH v hv)
  -- each member ticks to the vote time of slot `s₀ + 1`, active up to that tick from its tick to `tGAT + Δ S`
  have hwR : ∀ w ∈ Hon M S A x (s₀ + 1),
      w ∈ A.activeThroughoutToTick x ((tGAT + Δ S : ℕ) : ℤ) (M.voteTime S.C (s₀ + 1)) := by
    intro w hw
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R C.E (by omega)
      (by exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1) by omega)) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (hwA w hw)
    · push_cast; linarith
    · have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
      linarith
  have hkw : ∀ w ∈ Hon M S A x (s₀ + 1), ∃ kw : ℕ, x.lbl kw = Event.tick w (M.voteTime S.C (s₀ + 1)) ∧
      x.tickStep w (M.voteTime S.C (s₀ + 1)) = kw ∧
      x.time kw ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + ΔClockBehind := by
    intro w hw
    obtain ⟨kw, hkwl, -⟩ := Activity.mem_activeThroughoutToTick.1 (hwR w hw)
    exact ⟨kw, hkwl, (tickStep_eq_of_lbl M) x C.E hkwl, (C.E.tick_active kw w _ hkwl).2.2⟩
  intro w hw
  obtain ⟨kw, hkwl, hkw, hkwt⟩ := hkw w hw
  have hkw1 := (C.E.tick_active kw w _ hkwl).2.1
  set t : ℕ := M.slotStart S.C (s₀ + 1) - Δ S with ht
  have htD : t + Δ S = M.slotStart S.C (s₀ + 1) := by omega
  have hGt : GST + max (Δ S) Δs ≤ t + Δ S := by omega
  have hTt : tGAT + max (Δ S) Δs ≤ t + Δ S := by omega
  have hc0a : tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1 - S.C.k - 1) := by omega
  have hc0b : M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S ≤ t := by omega
  obtain ⟨k0, hk0l, -, hk0t⟩ := C.E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hpA
    (t := M.voteTime S.C (s₀ + 1 - S.C.k - 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) := by exact_mod_cast hc0a
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by omega)
  have hk0sb : k0 ≤ x.stepBefore t := by
    refine ((time_lt_iff_le_stepBefore M) x R C.E (by omega)).1 ?_
    have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) := by exact_mod_cast hc0b
    push_cast at this; linarith
  have hsbkp : x.stepBefore t ≤ kp := by
    refine (stepBefore_le_of_le_time_st M F) R C.E ?_
    have : ((t + Δ S : ℕ) : ℝ) = ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast htD
    push_cast at this; linarith
  have hfl1 := (floor_le_of_no_change_st M F) S A x R C.E p hsbkp
    (fun j h1 h2 => C.noChange M F R C.E p hk0l hlp (by omega) j (le_trans hk0sb h1) h2)
  have hkwE : x.time kw ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
    have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
    linarith
  -- F-P1-26-2: `w` read at its tick `kw` (`floor_le_of_delivery_tick_upTo`), the window from `a := t + Δ S − max (Δ S) Δs`, and
  -- `w`'s earlier tick to the start of slot `s₀ + 1`
  have hpt : p ∉ A.corruptedAtTime x t :=
    (not_mem_corruptedAtTime_of_le M) x R E (show t ≤ M.supportCutoff S.C (s₀ + 1) by omega) hpH
  have hsl : ∀ t' : ℕ, M.slot S.C t' = S.C.slot (t' : Int) := fun t' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslotp : ∀ Y ∈ (x.stateBefore t p).tree, M.slotStart S.C Y.slot ≤ M.slotStart S.C (s₀ + 1) := by
    intro Y hY
    have hi := (time_stepBefore_le M) x R E t
    have hvS : p ∉ A.corrupted (x.stepBefore t) :=
      (not_mem_corrupted_of_le_time M) x R E hpt (by exact_mod_cast hi)
    have h := (slot_le_clockValue_of_mem_tree M F) R E hvS hY
    have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore t) p
    have hcvR : (x.clockValue (x.stepBefore t) p : ℝ) < ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
      have h1 : ((t + Δ S : ℕ) : ℝ) = ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast htD
      have h2 : (1 : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ M.slotStart S.C (s₀ + 1) by omega)
      push_cast at h1
      refine lt_of_le_of_lt hcv (max_lt (by linarith) ?_)
      linarith
    have hlt := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout F.sched) S
      (Nat.cast_lt.1 hcvR)
    rw [hsl] at hlt
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (le_of_lt (h.trans_lt hlt))
  obtain ⟨hk₂, -, -⟩ := (tickStep_spec M) x R E (t := M.slotStart S.C (s₀ + 1)) (v := w) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by
        have h1 : ((tGAT + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show tGAT + max (Δ S) Δs ≤ M.slotStart S.C (s₀ + 1) by omega)
        have h2 : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hmx1
        push_cast at h1 h2 ⊢; linarith)
      (by
        have h1 : ((M.slotStart S.C (s₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
        push_cast at h1 ⊢; linarith)
      (hwA w hw))
  have hwin : ∀ i : ℕ, ((t + Δ S - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kw → w ∈ A.active i := by
    intro i h1 h2
    have h0 : ((tGAT : ℕ) : ℝ) ≤ ((t + Δ S - max (Δ S) Δs : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT ≤ t + Δ S - max (Δ S) Δs by omega)
    exact Activity.mem_activeThroughout.1 (hwA w hw) i (le_trans (R.time_mono h2) hkwE)
      (le_trans h0 (le_trans h1 (R.time_mono (Nat.le_succ i))))
  have hfl2 := (floor_le_of_delivery_tick_upTo M F U Fx) S A x R GST t (t + Δ S - max (Δ S) Δs) (M.voteTime S.C (s₀ + 1))
    (M.slotStart S.C (s₀ + 1)) kw (x.tickStep w (M.slotStart S.C (s₀ + 1))) p w C.E C.hNet C.hSkew C.hRedeliver C.Sy
    C.hRoots C.hParent (C.hThird.mono (le_trans hkwE (by exact_mod_cast hEs2))) (by omega) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by exact_mod_cast (show tGAT ≤ t + Δ S - max (Δ S) Δs by omega))
      (by exact_mod_cast (show t + Δ S - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s₀ + 1) by omega)) hpA)
    hpt hkwl (by omega) hwin hk₂ (by omega) hslotp (le_trans hkwE (le_add_of_nonneg_right C.E.behind_nonneg))
    (show M.voteTime S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
  have hTw : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st kw w := by
    unfold Trace.tickInput
    rw [hkw]
  rw [hTp, hTw]
  exact le_trans hfl1 hfl2

/-- **The round's base at the opening's first slot.** For the opening's proposal `B`, when no
opening's proposal collides with a block its proposer held and every member of
`Hon M S Sched (s₀ + 1)` has its finalized block, at its tick to the action time `M.supportCutoff S.C (s₀ + 2)`,
`B` or an ancestor of `B`: every member holds `B` at its tick to the vote time of slot `s₀ + 1`, the chain invariant
relative to `B` holds at slot `s₀ + 1` at `Hon M S Sched (s₀ + 1)`, and every member's update at its
tick to the action time saves `B` as its confirmation of slot `s₀ + 1` with `B` among its fast blocks
(`round_base_steps`, with the window's family, `fam` and `fam_parent`, the first clause and
`head_height_floor` at the proposer one delay before).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C (s₀ + 1 + 1)`: the bound of the
bundle `WinCtxUpTo`.

Every read is at the member's own tick (rule R3), as `round_base_steps` reads.

Read aloud: every member holds the proposal `B` at its tick to the vote time of slot `s₀ + 1`, the
chain invariant relative to `B` holds there, and every member's update at its tick to the action time
saves `B` with `B` among its fast blocks. -/
theorem base (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B)
    (hFinAr : ∀ v ∈ Hon M S A x (s₀ + 1),
      (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1))).finalized.AncestorEq B) :
    (∀ u ∈ Hon M S A x (s₀ + 1), B ∈ (x.tickInput u (M.voteTime S.C (s₀ + 1))).tree) ∧
    HonestChainExtends M S A x (Hon M S A x (s₀ + 1)) B (s₀ + 1) ∧
    ∀ v ∈ Hon M S A x (s₀ + 1), ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1)))
        ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1))) (s₀ + 1 + 1) →
      M.savedConfirmation n' (s₀ + 1) = some B ∧ B ∈ M.fastBlocks n' := by
  -- F-P1-28: `round_base_steps` at `s := s₀ + 1`, each row read at the reader's own tick (rule R3); the rows of the
  -- members' windows as `round89r` supplies them (`hMemWin`, `hMemRd`, `hMemAct`),'s `tStart := tGAT + Δ S`
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (C.cut_le M F) C.hEnd
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (by unfold aR; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by have := C.hrR; omega)) C.hEnd
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss1 : M.slotStart S.C (s₀ + 1 + 1) = M.slotStart S.C (s₀ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hvf1 := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hcm01 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ s₀)
  have hcm12 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ (s₀ + 1))
  have htl1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1)
  have htl2 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1 + 1)
  have hμs := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hvμ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 - S.C.k - 1)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hGSTt := C.hGST
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hsk := C.hSkew
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h := C.hΔs
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hk2 : 4 * Δ S * S.C.k ≤ 4 * Δ S * (S.C.k + 2) := Nat.mul_le_mul_left _ (by omega)
  have hcut : tGAT + 4 * Δ S * (S.C.k + 2) + 2 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
  have hm2 : tGAT + max (2 * Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
    rcases max_choice (2 * Δ S) Δs with h | h <;> rw [h] <;> omega
  have hm1 : tGAT + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpH : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := by
    have h := C.hSeq.honest i C.hi
    rw [C.hs] at h
    exact h
  have hpA := C.awakeHonest M F R C.E p (t₁ := tGAT) le_rfl hEs hpH
  obtain ⟨kp, hlp, hsp⟩ := id hB
  obtain ⟨-, hkp1, hkp2⟩ := C.E.tick_active kp p _ hlp
  have hTp : x.tickInput p (M.slotStart S.C (s₀ + 1)) = x.st kp p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x C.E hlp]
  -- the members of slot `s₀ + 1`: honest at the support cutoff of slot `s₀ + 2`, active from `tGAT` to it
  have hwH : ∀ w ∈ Hon M S A x (s₀ + 1), w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    fun w hw => (Finset.mem_sdiff.1 hw).2
  have hwA : ∀ w ∈ Hon M S A x (s₀ + 1), w ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    fun w hw => C.awakeHonest M F R C.E w (t₁ := tGAT) le_rfl hEs2 (hwH w hw)
  have hA2 : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1 + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hA1 : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hdw1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1) hA2
  have hAct : ∀ v ∈ Hon M S A x (s₀ + 1), v ∈ honestActiveAt M S A x (s₀ + 1) ∧ v ∈ updaterAt M S A x (s₀ + 1) :=
    fun v hv => C.hActive (s₀ + 1) (by omega) hEs2 v (hwH v hv)
  -- each member ticks to the vote time of slot `s₀ + 1`, active up to that tick from its tick to `tGAT + Δ S`
  have hwR : ∀ w ∈ Hon M S A x (s₀ + 1),
      w ∈ A.activeThroughoutToTick x ((tGAT + Δ S : ℕ) : ℤ) (M.voteTime S.C (s₀ + 1)) := by
    intro w hw
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R C.E (by omega)
      (by exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1) by omega)) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (hwA w hw)
    · push_cast; linarith
    · have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
      linarith
  have hkw : ∀ w ∈ Hon M S A x (s₀ + 1), ∃ kw : ℕ, x.lbl kw = Event.tick w (M.voteTime S.C (s₀ + 1)) ∧
      x.tickStep w (M.voteTime S.C (s₀ + 1)) = kw ∧
      x.time kw ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + ΔClockBehind := by
    intro w hw
    obtain ⟨kw, hkwl, -⟩ := Activity.mem_activeThroughoutToTick.1 (hwR w hw)
    exact ⟨kw, hkwl, (tickStep_eq_of_lbl M) x C.E hkwl, (C.E.tick_active kw w _ hkwl).2.2⟩
  -- the voters of the slots `s₀` and `s₀ + 1`
  have hMaj0 := (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x _ s₀ C.hCommittees hA1 (by omega)
  have hMaj1 := (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x _ (s₀ + 1) C.hCommittees hA2 hEs2
  have H := C.front M F R U Fx
  have hVot0 := H.voters M F R C.E U s₀ (by omega) le_rfl
  have hVot1 : ∀ u ∈ S.P.committee (s₀ + 1) ∩ Hon M S A x (s₀ + 1), u ∈ Hon M S A x (s₀ + 1) ∧
      u ∈ S.P.committee (s₀ + 1) ∧ ∃ vote : GoldfishVote V, vote.val_index = u ∧
        vote.slot = s₀ + 1 ∧ ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₀ + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x R (s₀ + 1) u C.E
      ((voteTime_tick_window_of_honestActiveAt M F U) S A x R (s₀ + 1) u C.E C.hSkew (hAct u huH).1)
    obtain ⟨vote, hvi, hvs, hsent⟩ := (honest_votes_of_window M F U) S A x R (s₀ + 1) u C.E hl hAw hK
    exact ⟨huH, hK, vote, hvi, hvs, k', hl, hsent⟩
  -- the family
  obtain ⟨hChain, hLocks, hAnchor, -, -⟩ := C.fam M F R E U Fx
  have hFamPar := C.fam_parent M F R E U Fx B hB
  have hcl1 := C.clause1 M F R E U Fx B hB
  set anchor := M.get_anchor (x.tickInput p (M.slotStart S.C (s₀ + 1))) ((M.slotStart S.C (s₀ + 1) : ℕ) : Int)
    with hanchor
  set Hs0 : Finset V := S.P.committee s₀ ∩ Hon M S A x s₀ with hHs0
  have hex : ∀ u ∈ Hs0, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s₀)).tree ∧ anchor.AncestorEq H_u := by
    intro u hu
    obtain ⟨huH, -, vote, -, -, i', hl, hsent⟩ := hVot0 u hu
    obtain ⟨H_u, hT, hvt, hAH⟩ := (hChain anchor hAnchor).1 u huH vote ⟨i', hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i', hl, hsent⟩, hT, hAH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun u => if h : u ∈ Hs0 then Hc u h else B
  have hHf : ∀ u (hu : u ∈ Hs0), Hf u = Hc u hu := fun u hu => dif_pos hu
  have hHsPrev : ∀ u ∈ Hs0, u ∈ S.P.committee (s₀ + 1 - 1) ∧
      (∀ w ∈ Hon M S A x (s₀ + 1), u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s₀ + 1)))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₀ + 1 - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₀ + 1 - 1) (Hf u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      Hf u ∈ (x.tickInput u (M.voteTime S.C (s₀ + 1 - 1))).tree ∧ anchor.AncestorEq (Hf u) := by
    intro u hu
    rw [Nat.add_sub_cancel]
    obtain ⟨huH, hK, -⟩ := hVot0 u hu
    rw [hHf u hu]
    refine ⟨hK, ?_, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
    intro w hw
    obtain ⟨kw, -, hkw, hkwt⟩ := hkw w hw
    rw [hkw]
    refine Activity.not_mem_corruptedAtTime.1 (Finset.mem_sdiff.1 huH).2 kw ?_
    have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
    linarith
  have hmem01 : ∀ w ∈ Hon M S A x (s₀ + 1), w ∈ Hon M S A x s₀ := fun w hw =>
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (s₀ + 1) (s₀ + 1 + 1) tAwakeEnd R C.E
      (Nat.le_succ _) hEs2).1 hw
  have hLocksW : ∀ w ∈ Hon M S A x (s₀ + 1), ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s₀ + 1)))
        ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s₀ + 1))) (s₀ + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s₀ + 1)))
          ((M.voteTime S.C (s₀ + 1) : ℕ) : Int) e = true → e.B.AncestorEq B.parent := by
    intro w hw n' sent hR' hAw e he hl
    obtain ⟨D, hD, heD⟩ := hLocks w (hmem01 w hw) n' sent hR' hAw e he hl
    exact ancestorEq_trans heD (hFamPar D hD)
  have hOnly : ∀ w ∈ Hon M S A x (s₀ + 1), ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C (s₀ + 1))).tree,
      B₁.slot = s₀ + 1 → B₁ = B := by
    intro w hw B₁ hB₁ hslot
    obtain ⟨kw, -, hkw, hkwt⟩ := hkw w hw
    have hpk : p ∉ A.corrupted kw := by
      refine Activity.not_mem_corruptedAtTime.1 hpH kw ?_
      have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
      linarith
    have hB₁' : B₁ ∈ (x.st kw w).tree := by
      have := hB₁
      unfold Trace.tickInput at this
      rw [hkw] at this
      exact this
    exact (GoldilocksCorrectness.Record.Proofs.Executions.only_block_of_unforgeability_st M F U) S A x R C.E (s₀ + 1)
      kw B B₁ p w hpk rfl hB hB₁' hslot
  have hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C (s₀ + 1))).tree, B₁.root ≠ B.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M x)]
    refine ⟨i, C.hi, B, ?_, ?_⟩
    · rw [C.hs]
      exact hB
    · rw [C.hs]
      rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold M x)]
      exact ⟨B₁, hB₁, heq⟩
  -- `head_height_floor` at the proposer's tick to the slot's start is at most each member's at its tick to the vote
  -- time: no change at the proposer from its last step before `t := slotStart (s₀ + 1) − Δ` to its tick, and
  -- `floor_le_of_delivery_tick_upTo` from before `t` to the member's tick
  have hFloorW : ∀ w ∈ Hon M S A x (s₀ + 1),
      M.head_height_floor (x.tickInput p (M.slotStart S.C (s₀ + 1))) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ≤
        (M.chainStateOf S.C B.parent).h := by
    intro w hw
    exact ⟨C.floor_le_member_tick M F R E U Fx B hB w hw, (hcl1 w hw).2⟩
  have hHeadP := (anchor_has_viable_head_st M F) S A x R C.E kp p
    (x.tickInput p (M.slotStart S.C (s₀ + 1))).lockEntries ((M.slotStart S.C (s₀ + 1) : ℕ) : Int)
  rw [← hTp, ← GoldilocksCorrectness.Record.get_anchor_eq_anchorAt F.rd] at hHeadP
  exact (GoldilocksCorrectness.Record.Proofs.Executions.round_base_steps_upTo M F U) S A x R GST (s₀ + 1) (Hon M S A x (s₀ + 1))
    (S.P.committee (s₀ + 1) ∩ Hon M S A x (s₀ + 1)) Hs0 Hf anchor B p _
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C (s₀ + 1))))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C (s₀ + 1))))
    C.E C.hNet C.hSkew C.hRedeliver C.Sy C.hΔs
    ((per_tick_roots_of_roots_until M F) x C.E C.hRoots le_rfl) C.hParent
    (votesCastByOwner_of_unforgeability M F S A x R C.E) (by omega)
    (by rw [Nat.add_sub_cancel]; omega)
    (fun v hv => (hAct v hv).2)
    (fun u hu hX => (Finset.mem_sdiff.1 (hAct u hu).1).2 (Finset.mem_union_right _ hX))
    (tGAT + Δ S)
    (by
      rw [Nat.add_sub_cancel]
      have hΔsC := C.hΔs
      have hcutR : ((tGAT : ℕ) : ℝ) + 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 2) + 2 * Δ S ≤
          ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hcut
      have hDk : (0 : ℝ) ≤ (Δ S : ℝ) * S.C.k := by positivity
      have hΔsR : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := by exact_mod_cast le_max_right (Δ S) Δs
      have hT0 : (0 : ℝ) ≤ (tGAT : ℝ) := by positivity
      have hk4 : 4 * Δ S * 4 ≤ 4 * Δ S * (S.C.k + 2) := Nat.mul_le_mul_left _ (by omega)
      have hN1 : tGAT + 4 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
      have hN2 : tGAT + Δs + 2 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
      have hN1R : ((tGAT + 4 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hN1
      have hN2R : ((tGAT + Δs + 2 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hN2
      push_cast at hN1R hN2R
      have h1 : (tGAT : ℝ) + Δ S + ΔClockAhead + ΔClockBehind + 2 * Δ S <
          ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by linarith
      have h2 : (tGAT : ℝ) + Δ S + ΔClockAhead + ΔClockBehind + Δs <
          ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by linarith
      have hm : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s₀ := by omega
      rw [Nat.cast_sub hm]
      push_cast
      have := max_lt (show (2 * (Δ S : ℝ)) < (M.supportCutoff S.C s₀ : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
        ΔClockBehind by linarith) (show (Δs : ℝ) < (M.supportCutoff S.C s₀ : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
        ΔClockBehind by linarith)
      linarith)
    (by
      have hle : tGAT + Δ S ≤ M.slotStart S.C (s₀ + 1) := by omega
      refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R C.E (by omega) (by exact_mod_cast hle) ?_
      refine Activity.mem_activeThroughout_of_le ?_ ?_ hpA
      · push_cast; linarith
      · have : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
        linarith)
    (Activity.mem_activeThroughout_of_le (by first | (norm_cast; omega) | norm_cast)
      (by first | (norm_cast; omega) | norm_cast) hpA)
    hwR ⟨kp, hlp, hsp⟩ hHsPrev
    (fun u hu => Activity.mem_activeThroughout_of_le
      (by simp only [Nat.add_sub_cancel]; norm_cast; omega)
      (by simp only [Nat.add_sub_cancel]; have := le_max_right (2 * Δ S) Δs; norm_cast; omega)
      (C.awakeHonest M F R C.E u (t₁ := tGAT) le_rfl hEs (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2))
    (fun w _ votes support_votes hCV =>
      ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R C.E s₀
        (x.tickStep w (M.voteTime S.C (s₀ + 1))) (Hon M S A x s₀) w hMaj0).2.2 votes support_votes hCV)
    (ancestorEq_refl _) hLocksW hOnly hRootNew hVot1
    (fun v _ => ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R C.E (s₀ + 1)
      (x.tickStep v (M.supportCutoff S.C (s₀ + 1 + 1))) (Hon M S A x (s₀ + 1)) v hMaj1).2.1)
    ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R C.E (s₀ + 1) 0
      (Hon M S A x (s₀ + 1)) p hMaj1).1
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) hFloorW
    (fun w hw => (hcl1 w hw).1)
    hFinAr hHeadP

end WinCtxUpTo

/-- `QuietCtx M S Sched x GST tGAT tAwakeEnd r m i rs s₀ s''`: the hypotheses of
`spoiled_near_fork_choice_change_cutoff` its proof reads, with the negation of its conclusion, for
the honest round opening slot `i` whose first slot is `s₀ + 1 = rs i * R` and the end `s''` of the
range read, at least one round later (`s₀ + 1 + R ≤ s''`, the field `sR`) and at most `r * R`: the
next honest round opening slot's first slot `rs (i + 1) * R`, or `r * R` for the honest round
opening slot whose round holds `r * R`: the execution assumptions and unforgeability,
every honest validator awake in the phase, fewer than a third in the adversary set, committee
sleepiness from `anchorCW S tGAT`, the honest round opening slots `rs 0 < … < rs m` with `i < m`
and `s'' ≤ r * R`, no proposal of an honest round opening slot colliding with a block its proposer
held, and no validator outside the adversary set with a `ForkChoiceChangeStep` at a step from the validator's own tick to the vote time of
slot `s₀ + 1 − k − 1` to before the support cutoff of slot `s''`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `s₀`: the slot before the honest round opening slot; `s''`: the
  end of the range read.

Roots name blocks until `ΔClockBehind` after `M.supportCutoff S.C s''`, where the members' ticks to it end: the end of the range read; every reader of the
bundle compares blocks held before times at most it.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of its roots
`hRoots`, the end of the range read; every reader of the bundle reads deliveries due by then.

Read aloud: the hypotheses of B10 that its proof reads, with the negation of its conclusion, with
the delivery premises up to the support cutoff of slot `s''`. -/
structure QuietCtxUpTo (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ) (s₀ s'' : ℕ) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- Blocks and Goldfish votes due by the bound are delivered within `Δ` after `GST`. -/
  E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s'')
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`, when that is at most the bound. -/
  Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject release ΔRedeliver Δs GST (M.supportCutoff S.C s'')
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  /-- Roots name blocks until `ΔClockBehind` after the support cutoff of slot `s''`, where the members' ticks to it end
. -/
  hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind)
  hParent : ParentHeldAtDelivery M x
  hGST : GST ≤ tGAT
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  /-- At every slot of the phase, every validator honest at the slot's update is an honest active validator and an
  updater of the slot. -/
  hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
    ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
      v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s
  hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd
  hEnd : aR M S r ≤ tAwakeEnd
  hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd
  hi : i < m
  hs : rs i * S.C.R = s₀ + 1
  sR : s₀ + 1 + S.C.R ≤ s''
  hir : s'' ≤ r * S.C.R
  hNoCol : ¬ RootCollisionAtOpening M S A x rs m
  hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1 - S.C.k - 1)) → k ≤ j →
    x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
    ¬ ForkChoiceChangeStep M S A x w j
  /-- -/
  htime : Monotone x.time

namespace QuietCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- The opening is at or after the first one.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: honest round opening slot `i`'s first slot is at least the first honest round opening
slot's. -/
theorem rs0 {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    rs 0 * S.C.R ≤ s₀ + 1 := by
  rw [← C.hs]
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact Nat.mul_le_mul_right _ (le_of_lt (r_lt_of_lt_of_mono rs m C.hSeq.mono 0 i h
      (le_of_lt C.hi)))

/-- Every window from the opening on starts after the committee premise's anchor.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle; `σ`: the last
  slot of the window.

Read aloud: every window ending at a slot from `s₀ + 1` on starts after the anchor of the committee
premise. -/
theorem win (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (h : s₀ + 1 ≤ σ) :
    2 * S.C.k ≤ σ ∧ anchorCW S tGAT ≤ M.slotStart S.C (σ - S.C.k - 1) := by
  have hw := (GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m tGAT tAwakeEnd σ C.hSeq (le_trans (C.rs0 M F) h)
  have h2 := hw.1
  have hk := S.C.k_ge_two
  exact ⟨h2, le_trans hw.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))⟩

/-- The support cutoff of the next opening's first slot is at most `aR M S r`.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: the support cutoff of slot `s''` is at most `aR M S r`. -/
theorem cut_le {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    M.supportCutoff S.C s'' ≤ aR M S r := by
  unfold aR
  have := C.hir
  exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)

/-- The support cutoff of the next opening's first slot is in the phase.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: the support cutoff of slot `s''` is at most `tAwakeEnd`. -/
theorem cut_end {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    M.supportCutoff S.C s'' ≤ tAwakeEnd :=
  le_trans (C.cut_le M F) C.hEnd

/-- No fork-choice change at `w` at a step from its own tick to the window's start clock value (the vote
time of slot `s₀ + 1 − k − 1`) to before one of its own ticks to a clock value at most the support cutoff of slot
`s''`.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `w`: the validator; `k`: the step of `w`'s tick to
  the window's start; `k'`, `c`: the step and the clock value of a later tick of `w`.

Read aloud: `w` has no fork-choice change at a step from its tick to the window's start to before one of its ticks
to a clock value at most the support cutoff of slot `s''`. -/
theorem noChange (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V) {k k' c : ℕ}
    (hk : x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1 - S.C.k - 1)))
    (hk' : x.lbl k' = Event.tick w c) (hc : c ≤ M.supportCutoff S.C s'') :
    ∀ j : ℕ, k ≤ j → j < k' → ¬ ForkChoiceChangeStep M S A x w j :=
  fun j hkj hjk => C.hNo w j k k' c hk hkj hk' hc hjk
    (E.not_mem_corrupted_of_le hjk.le ((Activity.mem_active.1 (E.tick_active k' w c hk').1).2))

/-- A validator honest at `b ≤ tAwakeEnd` is awake and honest at every time from `t₁ ≥ tGAT` to
`b`.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `w`: the validator; `t₁`, `b`: the times.

Read aloud: a validator honest at `b ≤ tAwakeEnd` is awake and honest at every time from `t₁ ≥ tGAT`
to `b`. -/
theorem awakeHonest (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V)
    {t₁ b : ℕ} (h1 : tGAT ≤ t₁) (hb : b ≤ tAwakeEnd) (hw : w ∉ A.corruptedAtTime x b) :
    w ∈ A.activeThroughout x t₁ b :=
  (mem_activeThroughout_of_hAwake_honest_at M F) R E C.hAwake h1 hb hw

/-- B6's context at the opening's window, the window ending at slot `s₀ + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle.

Read aloud: B6's bundle holds for the window ending at slot `s₀ + 1`. -/
theorem b6 (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    B6CtxUpTo M S A x GST tGAT tAwakeEnd r (s₀ + 1) Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet := by
  have h1 : s₀ + 1 ≤ s₀ + 1 := le_rfl
  have h2 : s₀ + 1 ≤ s'' := by have := C.sR; omega
  have hw := (C.win M F U) h1
  have hk2 := S.C.k_ge_two
  have hle : M.supportCutoff S.C (s₀ + 1) ≤ M.supportCutoff S.C s'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2
  have hBΔ : ΔClockBehind < Δ S := by linarith [C.hSkew, C.E.ahead_nonneg]
  have hsR := C.sR
  have hR := S.C.R_ge_two
  obtain ⟨-, hc1, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have h12 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ M.supportCutoff S.C s'' :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hB1 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) + ΔClockBehind < ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C s'' by omega)
    linarith
  exact
    { E := GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy.restrict C.E fun _ _ _ h => by
        obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
        exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2
          ⟨le_trans h1 (by exact_mod_cast hle), rfl⟩, hNet := C.hNet, hSkew := C.hSkew, hRedeliver := C.hRedeliver, Sy := C.Sy.mono hle,
      hΔs := C.hΔs, hRoots := (per_tick_roots_of_roots_until M F) x C.E ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_add_of_nonneg_right C.E.behind_nonneg) C.hRoots) hB1.le,
      hParent := C.hParent, hGST := C.hGST, hThird := C.hThird, hAwake := C.hAwake, hActive := C.hActive,
      hCommittees := C.hCommittees, hEnd := C.hEnd,
      hk := by have := hw.1; omega,
      hBefore := le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2) (C.cut_le M F),
      hTick := (tick_time_le_of_clock_le M F) x C.E
        (le_trans hB1.le (by exact_mod_cast le_trans (C.cut_le M F) C.hEnd)),
      hAnchor := le_trans hw.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)),
      hNo := (noChange_tick_end_mono M F) ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₀ + 1 ≤ s'' by have := C.sR; omega)) C.hNo }

/-- **B6's context at a later window, with roots until a later real time** (`QuietCtx.b6_at` with the delivery
premises up to `M.supportCutoff S.C s''`): for a slot `σ` from `s₀ + 1` to `s''` and roots naming blocks until a real
time `T` at least `ΔClockBehind` after the support cutoff of slot `σ`, B6's bundle holds at the window ending at slot
`σ`, its delivery premises restricted to the support cutoff of slot `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle; `σ`: the last slot of the window;
  `T`: the bound of the roots.

Read aloud: B6's bundle holds at every window ending at a slot of the range. -/
theorem b6_at (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {σ : ℕ} (h1 : s₀ + 1 ≤ σ) (h2 : σ ≤ s'') {T : ℝ} (hRootsT : RootsNameBlocksUntil M A x T)
    (hT : ((M.supportCutoff S.C σ : ℕ) : ℝ) + ΔClockBehind ≤ T) :
    B6CtxUpTo M S A x GST tGAT tAwakeEnd r σ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet := by
  have hw := (C.win M F U) h1
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hk2 := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hsR := C.sR
  have hir := C.hir
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hcσ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2
  have hcσR := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (le_trans h2 hir)
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R) + 4 * Δ S := by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S _
  have hEnd := C.hEnd
  -- every tick to a clock value at most the support cutoff of slot `σ` is in the phase
  have hTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C σ →
      x.time k ≤ (tAwakeEnd : ℝ) :=
    (tick_time_le_of_clock_le M F) x C.E (T := (tAwakeEnd : ℝ)) (by
      have : ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C σ + Δ S ≤ tAwakeEnd by omega)
      linarith [C.hSkew])
  -- the vote time of slot `σ − k − 1` is `4 (σ − s₀ − 1)` delays after that of slot `s₀ + 1 − k − 1`
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hvt : M.voteTime S.C (σ - S.C.k - 1) =
      M.voteTime S.C (s₀ + 1 - S.C.k - 1) + 4 * (σ - (s₀ + 1)) * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 - S.C.k - 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ + 1 - S.C.k - 1)]
    have hσd : σ - S.C.k - 1 = (s₀ + 1 - S.C.k - 1) + (σ - (s₀ + 1)) := by omega
    rw [hσd]
    ring
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 - S.C.k - 1)
  have hTv : tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1 - S.C.k - 1) := by
    rw [hv0]
    have : tGAT ≤ tGAT + 4 * Δ S * (S.C.k + 2) := Nat.le_add_right _ _
    omega
  exact
    { E := GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy.restrict C.E fun _ _ _ h => by
        obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
        exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2
          ⟨le_trans h1 (by exact_mod_cast hcσ), rfl⟩, hNet := C.hNet, hSkew := C.hSkew, hRedeliver := C.hRedeliver, Sy := C.Sy.mono hcσ,
      hΔs := C.hΔs, hRoots := (per_tick_roots_of_roots_until M F) x C.E hRootsT hT,
      hParent := C.hParent, hGST := C.hGST, hThird := C.hThird, hAwake := C.hAwake, hActive := C.hActive,
      hCommittees := C.hCommittees, hEnd := C.hEnd,
      hk := by have := hw.1; omega,
      hBefore := le_trans hcσ (C.cut_le M F),
      hTick := hTick,
      hAnchor := le_trans hw.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)),
      hNo := by
        intro w j k k' c hk hkj hk' hc hjk' hwj
        have hwk : w ∉ A.corrupted k := C.E.not_mem_corrupted_of_le hkj hwj
        have hkE : x.time k ≤ tAwakeEnd :=
          le_trans ((time_mono M) x R (le_trans hkj hjk'.le)) (hTick k' w c hk' hc)
        rw [hvt] at hk
        obtain ⟨k₀, hk₀k, hk₀⟩ := (tick_before_of_tick_in_phase_mul M F) S A x R C.E C.hSkew C.hAwake
          (4 * (σ - (s₀ + 1))) _ w k hTv hk hkE hwk
        exact C.hNo w j k₀ k' c hk₀ (le_trans hk₀k hkj) hk' (le_trans hc hcσ) hjk' hwj }

end QuietCtxUpTo

namespace QuietCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- The window's context of the opening.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: the bundle of an honest round opening slot's range gives the bundle of its window. -/
theorem toWin {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    WinCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet := by
  have hsR := C.sR
  have hir := C.hir
  have hR := S.C.R_ge_two
  have hle : M.supportCutoff S.C (s₀ + 1 + 1) ≤ M.supportCutoff S.C s'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  exact
    { E := GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy.restrict C.E fun _ _ _ h => by
        obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
        exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2
          ⟨le_trans h1 (by exact_mod_cast hle), rfl⟩,
      hNet := C.hNet, hSkew := C.hSkew, hRedeliver := C.hRedeliver, Sy := C.Sy.mono hle, hΔs := C.hΔs,
      hRoots := (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by
          have h := (show ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) from by exact_mod_cast hle)
          linarith [C.E.behind_nonneg]) C.hRoots,
      hParent := C.hParent, hGST := C.hGST, hThird := C.hThird, hAwake := C.hAwake, hActive := C.hActive,
      hCommittees := C.hCommittees, hEnd := C.hEnd, hSeq := C.hSeq, hi := le_of_lt C.hi, hs := C.hs, hrR := by omega,
      hNo := (noChange_tick_end_mono M F) ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₀ + 1 ≤ s'' by have := C.sR; omega)) C.hNo }

/-- **The round's first clause**
(`WinCtx.clause1`).

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle; `B`: the proposal.

Read at each member's tick input to the vote time.

Read aloud: in the state its tick to the vote time of slot `s₀ + 1` starts from, every member's root
is `B.parent` or an ancestor of it, with `head_height_floor` at most `B.parent`'s chain-state
height. -/
theorem clause1 (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∀ w ∈ Hon M S A x (s₀ + 1),
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (s₀ + 1)))).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ≤
        (M.chainStateOf S.C B.parent).h :=
  (C.toWin M F).clause1 M F R E U Fx B hB

end QuietCtxUpTo

namespace QuietCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- **The proposal and its parent, at the proposer.** The opening's proposal `B` has a parent that
is a viable head of the frame of the state the proposer's tick to the start of slot `s₀ + 1` reads,
held in that state (`proposal_parent_viable_head`); its parent is an ancestor of it, at a
chain-state height at most `B`'s.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: the proposal's parent is a viable head of what the proposer's tick to the start of slot
`s₀ + 1` reads, held there, and an ancestor of the proposal at a chain-state height at most its. -/
theorem proposal_facts (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    B.parent ∈ (M.fg_to_ac (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
    B.parent ∈ (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))).tree ∧
    B.parent.AncestorEq B ∧ (M.chainStateOf S.C B.parent).h ≤ (M.chainStateOf S.C B).h := by
  have hPV := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_parent_viable_head M F U) S A x R E s₀ B _ hB
  obtain ⟨iB, hl, hsent⟩ := hB
  have hPV' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
    ((nodeInv_tickInput_of_tick M F) S A x R E hl) _).1 hPV
  obtain ⟨-, hBne, hBpar?, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_parent_walk_end M F U) S A x R E s₀ iB B _ hl hsent
  have hPB : B.parent.AncestorEq B := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hBpar?
  have hh : (M.chainStateOf S.C B.parent).h ≤ (M.chainStateOf S.C B).h := by
    rcases ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).2.1 hBne with h | h
    · rw [h]
    · rw [h]
      exact Nat.le_succ _
  exact ⟨hPV, hPV'.1, hPB, hh⟩

/-- **The opening's proposal is put on the wire at its proposer's tick, and held right after it.**
For the opening's proposal `B`: some step `i` is the tick of the proposer of slot `s₀ + 1` at the
start of that slot, puts `B` on the wire, and leaves the proposer holding `B`
(`lem22a_proposer_holds_own_proposal`, the root of `B` new to the proposer since no opening
collides, `B`'s parent a viable head of the proposer).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: the proposer sends the proposal at its tick at the start of slot `s₀ + 1` and holds it
right after that tick. -/
theorem proposal_sent (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∃ iB : ℕ, x.lbl iB = Event.tick (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)) ∧
      (⟨S.P.proposer (s₀ + 1), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (iB + 1) - x.sent iB ∧
      B ∈ (x.st (iB + 1) (S.P.proposer (s₀ + 1))).tree := by
  obtain ⟨iB, hl, hsent⟩ := hB
  have hPV := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_parent_viable_head M F U) S A x R E s₀ B _
    ⟨iB, hl, hsent⟩
  have hPV' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
    ((nodeInv_tickInput_of_tick M F) S A x R E hl) _).1 hPV
  obtain ⟨-, -, hBpar?, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_parent_walk_end M F U) S A x R E s₀ iB B _ hl hsent
  have hPB : B.parent.AncestorEq B := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hBpar?
  -- no block of the proposer's tick input has `B`'s root: the openings do not collide
  have hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))).tree,
      B'.root ≠ B.root := by
    intro B' hB' heq
    apply C.hNoCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M x)]
    refine ⟨i, le_of_lt C.hi, B, ?_, ?_⟩
    · rw [C.hs]
      exact ⟨iB, hl, hsent⟩
    · rw [C.hs]
      exact ⟨B', hB', heq⟩
  have hF : (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))).finalized.compatible B =
      true := (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV'.2.1 hPB))
  exact ⟨iB, hl, hsent, (GoldilocksCorrectness.Record.Proofs.Executions.lem22a_proposer_holds_own_proposal M F U)
    S A x R s₀ iB B _ E hl hsent hRootNew hPV'.1 hF⟩

/-- **A member's root stays on the proposal's parent's chain through the context's range, read at
its ticks.** For a member `w` of `Hon M S Sched (s₀ + 1)` and a clock value `t₂` from the vote time
of slot `s₀ + 1` to the support cutoff of slot `s''` to which `w` ticks at the step `kt`:
in the state `w`'s tick to `t₂` starts from, its root is `B.parent` or an ancestor of it, with its `head_height_floor` at
most `B.parent`'s height. It is read at the tick input; the form read before a real time had no route and no reader (F-P1-29).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal; `w`: the member; `t₂`: the clock value.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: through the range read, in the state each of its ticks starts from, a member's root
stays `B.parent` or an ancestor of it, with `head_height_floor` at most `B.parent`'s chain-state
height. -/
theorem rootBelow_tick (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) (w : V) (hw : w ∈ Hon M S A x (s₀ + 1)) (t₂ : ℕ)
    (h1 : M.voteTime S.C (s₀ + 1) ≤ t₂) (h2 : t₂ ≤ M.supportCutoff S.C s'')
    (kt : ℕ) (hkt : x.lbl kt = Event.tick w t₂) :
    (M.get_fc_root (x.tickInput w t₂)).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w t₂) ≤ (M.chainStateOf S.C B.parent).h := by
  -- `clause1` at `w`'s tick to the vote time of slot `s₀ + 1`, then `root_below_kept_st` from that tick to `w`'s tick
  -- to `t₂`, over the no-change window `C.hNo` (from `w`'s tick to the window's start value, before the support
  -- cutoff of slot `s''`)
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hsR := C.sR
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEnd := C.cut_end M F
  have hanc := hw0.2
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hanc
  obtain ⟨hv1, hc1, -, hs1, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc2 := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)).2.1
  have hv0 := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
    (s₀ + 1 - S.C.k - 1)).1
  have hss0 : M.slotStart S.C (s₀ + 1 - S.C.k - 1) + 4 * Δ S * (S.C.k + 1) = M.slotStart S.C (s₀ + 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), ← Nat.mul_add]
    congr 1
    have := hw0.1
    omega
  have h12 : 4 * Δ S * 3 ≤ 4 * Δ S * (S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hcm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀ + 1 + 1 ≤ s'' by omega)
  have hA0 := E.ahead_nonneg
  have hSkew := C.hSkew
  have hB0 := E.behind_nonneg
  -- `w`'s ticks to the window's start value and to the vote time of slot `s₀ + 1`
  have hwH : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) := (Finset.mem_sdiff.1 hw).2
  have hwA := C.awakeHonest M F R E w (t₁ := tGAT) le_rfl (le_trans hcm hEnd) hwH
  obtain ⟨k0, hk0l, -, hk0t⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hwA
    (t := M.voteTime S.C (s₀ + 1 - S.C.k - 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) := by
        exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by omega)
  obtain ⟨kv, hkvl, hkvt, -⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hwA
    (t := M.voteTime S.C (s₀ + 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by omega)
  have hk0kv : k0 ≤ kv := by
    refine ((lt_of_time_lt M) x R ?_).le
    have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show _ ≤ _ by omega)
    push_cast at this; linarith
  have hTv : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st kv w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkvl]
  obtain ⟨hr1, hf1⟩ := (C.clause1 M F R E U Fx) B hB w hw
  rw [hTv] at hr1 hf1
  -- the proposer holds `B.parent` at its tick to the start of slot `s₀ + 1`
  obtain ⟨kp, hlp, hsp⟩ := id hB
  obtain ⟨hpact, -, hkp2⟩ := E.tick_active kp _ _ hlp
  have hPV := (proposal_parent_viable_head M F U) S A x R E s₀ B _ ⟨kp, hlp, hsp⟩
  have hTp : x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)) = x.st kp (S.P.proposer (s₀ + 1)) := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hlp]
  rw [hTp] at hPV
  obtain ⟨hXp, -⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
    (show M.nodeInvCore S.C S.P S.X (x.st kp (S.P.proposer (s₀ + 1))) from
      (lem11_node_invariantCore_of_run M F S x R kp _).1) B.parent).1 hPV
  have hkpE : x.time kp ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
    have : ((M.slotStart S.C (s₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
      exact_mod_cast (show _ ≤ _ by omega)
    push_cast at this; linarith
  -- `w`'s tick to `t₂`
  obtain ⟨hact, -, hkt2⟩ := E.tick_active kt w t₂ hkt
  have hwkt : w ∉ A.corrupted kt := (Activity.mem_active.1 hact).2
  have hwkv : w ∉ A.corrupted kv := (Activity.mem_active.1 (E.tick_active kv w _ hkvl).1).2
  have hkvkt : kv ≤ kt := by
    by_contra hlt
    push Not at hlt
    have hle := E.clock_mono kt kv w t₂ (M.voteTime S.C (s₀ + 1)) hlt hwkv (Or.inl hkt) (Or.inl hkvl)
    have heq : t₂ = M.voteTime S.C (s₀ + 1) := le_antisymm hle h1
    rw [heq] at hkt
    have := E.tick_unique kt kv w _ hkt hkvl
    omega
  -- the steps read are at real times at most `ΔClockBehind` after the support cutoff of slot `s''`, where the roots
  -- premise ends; the adversary bound is read until one delay after that cutoff
  have hSk' := C.hSkew
  have hA0' := C.E.ahead_nonneg
  have hB0' := C.E.behind_nonneg
  have hcutΔ : M.supportCutoff S.C s'' + Δ S ≤ tAwakeEnd := by
    have hs1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (r * S.C.R)
    have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S C.hir
    have hs3 := C.hEnd
    unfold aR at hs3
    omega
  have hktR : x.time kt ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind := by
    have : ((t₂ : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have hktE : x.time kt ≤ ((M.supportCutoff S.C s'' + Δ S : ℕ) : ℝ) := by
    push_cast; linarith
  have hkpE' : x.time kp ≤ ((M.supportCutoff S.C s'' + Δ S : ℕ) : ℝ) := by
    push_cast; linarith
  have hTt : x.tickInput w t₂ = x.st kt w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkt]
  rw [hTt]
  exact (root_below_kept_st M F Fx) S A x R E C.hRoots (M.supportCutoff S.C s'' + Δ S) kv kt kp w _ B.parent
    (C.hThird.mono (by exact_mod_cast hcutΔ)) hkpE' ((Activity.mem_active.1 hpact).2) hXp hkvkt hktE hwkt hr1 hf1
    (fun j h1' h2' => C.hNo w j k0 kt t₂ hk0l (le_trans hk0kv h1') hkt (by omega) h2'
      (E.not_mem_corrupted_of_le h2'.le hwkt))
    (by linarith) hktR

/-- **The round's second clause, read at the members' ticks.** In the state its tick to the action
time of slot `s₀ + 1` starts from, every member has its root `B` or an ancestor of `B` and its
`head_height_floor` at most `B`'s height (`rootBelow_tick`). It is read at the tick input
, the second clause of `QuietRoundOnConfirmations`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: in the state its tick to the action time of slot `s₀ + 1` starts from, every member's
root is `B` or an ancestor of `B`, with `head_height_floor` at most `B`'s chain-state height. -/
theorem clause2_tick (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∀ v ∈ Hon M S A x (s₀ + 1),
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1)))).AncestorEq B ∧
      M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1))) ≤
        (M.chainStateOf S.C B).h := by
  intro v hv
  have hsR := C.sR
  have hR := S.C.R_ge_two
  obtain ⟨-, -, hPB, hh⟩ := (C.proposal_facts M F R E U) B hB
  have hvb : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) := (Finset.mem_sdiff.1 hv).2
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hA : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1 + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
    (s₀ + 1) hA
  -- `v` is an updater of slot `s₀ + 1`, so it ticks to the support cutoff of slot `s₀ + 2`
  obtain ⟨kt, hkt, -⟩ := Activity.mem_activeThroughoutToTick.1 (C.hActive (s₀ + 1) (by omega)
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
      (C.cut_end M F)) v hvb).2
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hv12 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s₀ + 1)
  obtain ⟨hr, hf⟩ := (C.rootBelow_tick M F R E U Fx) B hB v hv (M.supportCutoff S.C (s₀ + 1 + 1)) (by omega)
    (by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ + 1 + 1 + 1 ≤ s'' by omega)
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1 + 1)).2.1
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)).2.2.2.1
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)).2.1
      omega) kt hkt
  exact ⟨ancestorEq_trans hr hPB, le_trans hf hh⟩

/-- **The round's third clause.** At every slot `s'` of the round with `s' + 2 ≤ s''`, every member
of `Hon M S Sched (s' + 1)` satisfies `StepFrameAt` relative to the proposal `B`: `B` reaches it one
delay after its proposer's tick (`proposal_held_at_later_tick`), and its root stays on `B`'s
parent's chain with its `head_height_floor` at most `B`'s height (`rootBelow_tick`), at the two reading
points (`stepFrame_of_compat`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: at every slot of the range, every member satisfies `StepFrameAt` relative to the
proposal `B`. -/
theorem clause3 (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    ∀ s', s₀ + 1 ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon M S A x (s' + 1),
      StepFrameAt M S A x B s' w := by
  intro s' h1 h2 w hw
  -- F-P1-33: `w`'s tick `k` to the vote time of slot `s₀ + 1` holds `B` (`proposal_held_at_later_tick`), its ticks to
  -- the vote time of slot `s' + 1` and to the support cutoff of slot `s' + 2` read `rootBelow_tick`
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  obtain ⟨hgA, hE2, hgV, hVC, hgV', hVC', hvv, hv'E, hcE, hvf, hsv, hvE, hGv, hcc, hanc2⟩ :=
    (stepFrame_times M F U) S hw0.2 C.hGST h1 h2 (C.cut_end M F)
  have hwb : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s' + 1 + 1)) := (Finset.mem_sdiff.1 hw).2
  have hw1 : w ∈ Hon M S A x (s₀ + 1) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (not_mem_corruptedAtTime_of_le M) x R C.E hcc hwb⟩
  have hwA := (C.awakeHonest M F R C.E) w (t₁ := tGAT) (b := M.supportCutoff S.C (s' + 1 + 1)) le_rfl hE2 hwb
  have tick : ∀ t : ℕ, tGAT + Δ S ≤ t → t + Δ S ≤ M.supportCutoff S.C (s' + 1 + 1) →
      x.lbl (x.tickStep w t) = Event.tick w t := by
    intro t ht1 ht2
    exact ((tickStep_spec M) x R C.E (t := t) (v := w) (le_trans hΔ (le_trans (Nat.le_add_left _ _) ht1))
      (Activity.mem_activeThroughout_of_le
        (by have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((t : ℕ) : ℝ) := by exact_mod_cast ht1
            linarith)
        (by have : ((t : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast ht2
            linarith) hwA)).1
  obtain ⟨k, hkl⟩ : ∃ k, x.lbl k = Event.tick w (M.voteTime S.C (s₀ + 1)) :=
    ⟨_, tick (M.voteTime S.C (s₀ + 1)) hgV hVC⟩
  have hkv := tick (M.voteTime S.C (s' + 1)) hgV' hVC'
  -- `w` is an updater of slot `s' + 1`, so it ticks to the support cutoff of slot `s' + 2`
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
    (s' + 1) hanc2
  obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 (C.hActive (s' + 1) (le_trans (Nat.le_add_right _ _) hdw) hE2 w hwb).2
  obtain ⟨hr1, hf1⟩ := (C.rootBelow_tick M F R E U Fx) B hB w hw1
    (M.voteTime S.C (s' + 1)) hvv hv'E _ hkv
  obtain ⟨hr2, -⟩ := (C.rootBelow_tick M F R E U Fx) B hB w hw1
    (M.supportCutoff S.C (s' + 1 + 1)) (le_trans (Nat.le_add_right _ _) hVC) hcE k2 hk2
  -- `clause1` at the tick `k`: the root is on `B.parent`'s chain, so the finalized block is compatible with `B`
  obtain ⟨hr0, -⟩ := (C.clause1 M F R E U Fx) B hB w hw1
  have hTk : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st k w := by
    show x.st (x.tickStep w (M.voteTime S.C (s₀ + 1))) w = x.st k w
    rw [(tickStep_eq_of_lbl M) x C.E hkl]
  rw [hTk] at hr0
  have hkT := ((time_of_lbl_tick M) x R C.E hkl).1
  have hwin : ∀ j : ℕ, (M.slotStart S.C (s₀ + 1) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ k → w ∈ A.active j := by
    intro j hj1 hj2
    refine Activity.mem_activeThroughout.1 hwA j ?_ ?_
    · have : x.time j ≤ x.time k := htime hj2
      have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast hVC
      linarith
    · have : x.time j ≤ x.time (j + 1) := htime (Nat.le_succ j)
      have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hgA
      linarith
  have hv0 : 0 < M.voteTime S.C (s₀ + 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hΔ) (le_trans (Nat.le_add_left _ _) hgV)
  have hsvR : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hsv
  have hvc : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by exact_mod_cast hvE
  obtain ⟨-, -, hPB, hh⟩ := (C.proposal_facts M F R E U) B hB
  obtain ⟨iB, hl, hsent, hBi⟩ := (C.proposal_sent M F R E U) B hB
  -- the deadline of the proposer's send, within the bound and `ΔClockAhead` before the vote time of slot `s₀ + 1`
  have hTi1 := ((time_of_lbl_tick M) x R C.E hl).2.2
  have hNt := C.hNet
  have hsvΔ : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_eq
      ((GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)).symm
  have hGs : ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_trans C.hGST (le_trans (Nat.le_add_right _ _) hgA)
  have hmax : max (x.time (iB + 1)) ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + ΔClockBehind :=
    max_le hTi1 (by linarith)
  have hBk : B ∈ (x.st k w).tree :=
    (proposal_held_at_later_tick_of_deadline M F U) S A x R s₀ iB k (M.voteTime S.C (s₀ + 1)) B (S.P.proposer (s₀ + 1)) w
      C.E C.hSkew C.hRedeliver
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith [hkT.2]) C.hRoots)
      C.hParent le_rfl hkl hwin hl hsent hBi
      (GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans
        ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R C.E k w)
        (ancestorEq_trans hr0 hPB))))
  exact (stepFrame_of_compat M F U) S A x R C.E B B s' w (ancestorEq_refl B) hkl
    ((clockValue_lt_of_tick_of_active M F) C.E hkl hv0 (fun j hj1 hj2 => hwin j (by linarith) hj2))
    hvf (by rw [hTk]; exact hBk) hkv ((tick_step_le_of_le M F) C.E hkl hkv hvv)
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hr1 hPB))) (le_trans hf1 hh)
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hr2 hPB)))

/-- **The round's fourth clause.** At every slot `s'` from `s₀` with `s' + 2 ≤ s''`, every member
of `Hon M S Sched (s' + 1)` satisfies `StepFrameAt` relative to every confirmation `X` of a slot `σ`
from `s₀` to `s'` that a member of `Hon M S Sched σ` saved: `X` has an honest committee supporter
whose vote's block is an ancestor of a block `W` that `w` holds one delay after the vote time of
slot `σ`, with `w`'s root compatible with `W` and its `head_height_floor` at most `W`'s height then
(B6's `frame` at the window ending at slot `σ + 2`); both stay so through the range
(`frame_compat_kept`), and `stepFrame_of_compat` at the two reading points.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: at every slot of the range, every member satisfies `StepFrameAt` relative to every
confirmation a member saved from slot `s₀` on. -/
theorem clause4 (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    ∀ s', s₀ + 1 - 1 ≤ s' → s' + 2 ≤ s'' → ∀ σ, s₀ + 1 - 1 ≤ σ → σ ≤ s' →
      ∀ v ∈ Hon M S A x σ, ∀ X : Block V,
        (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X →
        ∀ w ∈ Hon M S A x (s' + 1), StepFrameAt M S A x X s' w := by
  intro s' h1 h2 σ h3 h4 v hv X hX w hw
  -- B6's `supporter_saved` and `frame_st` at the window ending at slot `σ + 2`, `w` read at its ticks to the vote time
  -- of slot `s' + 1` and to the support cutoff of slot `s' + 2` (no change from its tick to the window's start), `X`
  -- held through the block `W` of `w`'s tick to the support cutoff of slot `σ`; `stepFrame_of_compat`
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have h3' : s₀ ≤ σ := le_trans (Nat.le_of_eq (Nat.add_sub_cancel s₀ 1).symm) h3
  obtain ⟨hE2, hEΔ, hgK, hKC, hgc, hcC, hgV, hVC, hanc2, hcf, hcv, hσb, hbC, hσV, hVE, hCE, hσE, hKσ, hbE⟩ :=
    (confirmFrame_times M F U) S hw0.2 h3' h4 h2 C.hir C.hEnd
  have hwb : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s' + 1 + 1)) := (Finset.mem_sdiff.1 hw).2
  have hwA := (C.awakeHonest M F R C.E) w (t₁ := tGAT) (b := M.supportCutoff S.C (s' + 1 + 1)) le_rfl hE2 hwb
  have tick : ∀ t : ℕ, tGAT + Δ S ≤ t → t + Δ S ≤ M.supportCutoff S.C (s' + 1 + 1) →
      x.lbl (x.tickStep w t) = Event.tick w t := by
    intro t ht1 ht2
    exact ((tickStep_spec M) x R C.E (t := t) (v := w) (le_trans hΔ (le_trans (Nat.le_add_left _ _) ht1))
      (Activity.mem_activeThroughout_of_le
        (by have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((t : ℕ) : ℝ) := by exact_mod_cast ht1
            linarith)
        (by have : ((t : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast ht2
            linarith) hwA)).1
  have hk0 := tick _ hgK hKC
  obtain ⟨k, hkl⟩ : ∃ k, x.lbl k = Event.tick w (M.voteTime S.C σ + Δ S) := ⟨_, tick _ hgc hcC⟩
  have hkv := tick _ hgV hVC
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
    (s' + 1) hanc2
  obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1
    (C.hActive (s' + 1) (le_trans (Nat.le_add_right _ _) hdw) hE2 w hwb).2
  -- B6's bundle at the window ending at slot `σ + 2`
  have C6 : B6CtxUpTo M S A x GST tGAT tAwakeEnd r (σ + 2) Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet :=
    (C.b6_at M F R U) (le_trans (Nat.succ_le_succ h3') (Nat.le_succ _))
    (le_trans (Nat.add_le_add_right h4 2) h2) C.hRoots
    (by have : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by exact_mod_cast hbE
        linarith)
  have hσK : σ + 2 - S.C.k - 1 ≤ σ := by have := S.C.k_ge_two; clear * - this; omega
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ :=
    (C6.supporter_saved M F R E U) hσK le_rfl v hv X hX
  -- the frame at the step `i` of `w`, for `i` a tick of `w` to a clock value from the vote time of slot `s' + 1` to the
  -- support cutoff of slot `s''`
  have hσbR : (((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ)) + Δ S ≤ ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) := by
    exact_mod_cast hσV
  have hk0T := (C.E.tick_active _ w _ hk0).2.2
  have hk0b : x.tickStep w (M.voteTime S.C (s₀ + 1 - S.C.k - 1)) < x.stepBefore (M.voteTime S.C σ + 2 * Δ S) := by
    refine (lt_stepBefore_of_not_other M) x R C.E (by rw [hk0]; simp) ?_
    have : ((M.voteTime S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) := by
      exact_mod_cast hKσ
    linarith
  have hwσ : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2)) := (not_mem_corruptedAtTime_of_le M) x R C.E hbC hwb
  have frameAt : ∀ (c i : ℕ), M.voteTime S.C (s' + 1) ≤ c → c ≤ M.supportCutoff S.C s'' → x.lbl i = Event.tick w c →
      ∃ H₁ ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H₁.root ∧
        ∃ W : Block V, H₁.AncestorEq W ∧ W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree ∧
          M.head_height_floor (x.st i w) ≤ (M.chainStateOf S.C W).h ∧
          (x.st i w).finalized.compatible W = true ∧
          (M.get_fc_root (x.st i w)).compatible W = true := by
    intro c i hc1 hc2 hi
    have hiT := (C.E.tick_active i w c hi).2
    have hcR : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hc2R : (c : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by exact_mod_cast hc2
    have hEΔR : ((M.supportCutoff S.C s'' : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEΔ
    exact (C6.frame_st M F R U Fx) hσK le_rfl u huA vote hsend w (M.supportCutoff S.C (σ + 2)) hσb le_rfl hwσ i
      (by linarith [hiT.2]) ((stepBefore_lt_of_le_time M) x R C.E (by clear * - hΔ; omega) (by linarith [hiT.1])).le
      (C.E.not_mem_corrupted_of_tick hi)
      (fun j hj hji => (C.noChange M F R C.E) w hk0 hi hc2 j (le_trans hk0b.le hj) hji) C.hRoots
      (by linarith [hiT.2])
  -- `vote` names one block of `u`'s tree at its tick
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hsend
    exact x.lbl_tickStep ⟨i, hi⟩
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := C.E.not_mem_corrupted_of_tick hkU
  have hkUT : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind := by
    have h := (C.E.tick_active _ u _ hkU).2.2
    have : ((M.voteTime S.C σ : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_right _ _) hσE
    linarith
  have hsame : ∀ H₁ ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H₁.root → H₁ = H_u := by
    intro H₁ hH₁T hv₁
    rw [hvote] at hv₁
    simp only [GoldfishVote.mk.injEq, true_and] at hv₁
    exact C.hRoots H₁ H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (i := x.tickStep u (M.voteTime S.C σ)) (v := u) huk hkUT hH₁T) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (i := x.tickStep u (M.voteTime S.C σ)) (v := u) huk hkUT hHT) hv₁.symm
  obtain ⟨H₁, hH₁T, hv₁, W, hHW, hWT, hf1, -, hr1⟩ := frameAt _ _ le_rfl hVE hkv
  obtain ⟨H₂, hH₂T, hv₂, W₂, hHW₂, -, -, hF2, -⟩ := frameAt _ _ (le_trans (Nat.le_add_right _ _) hVC) hCE hk2
  rw [hsame H₁ hH₁T hv₁] at hHW
  rw [hsame H₂ hH₂T hv₂] at hHW₂
  have hXW := ancestorEq_trans hXH hHW
  -- the finalized block at the tick `k2` is compatible with `W₂`, a descendant of `X`, so with `X`
  have hfin : (x.tickInput w (M.supportCutoff S.C (s' + 2))).finalized.compatible X = true := by
    have hTc : x.tickInput w (M.supportCutoff S.C (s' + 2)) = x.st k2 w := by
      show x.st (x.tickStep w (M.supportCutoff S.C (s' + 2))) w = x.st k2 w
      rw [(tickStep_eq_of_lbl M) x C.E (t := M.supportCutoff S.C (s' + 2)) hk2]
    rw [hTc]
    rcases (compatible_iff _ _).1 hF2 with hRW | hWR
    · exact (compatible_iff _ _).2 (ancestorEq_compatible hRW (ancestorEq_trans hXH hHW₂))
    · exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans (ancestorEq_trans hXH hHW₂) hWR))
  -- `w`'s tick `k` to the support cutoff of slot `σ` holds `W`, from a smaller clock value
  have hcR : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcC
  have hgcR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) := by exact_mod_cast hgc
  have hkT := (C.E.tick_active k w _ hkl).2
  have hlt := (clockValue_lt_of_tick_of_active M F) C.E hkl
    (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hΔ) (le_trans (Nat.le_add_left _ _) hgc))
    (fun j hj1 hj2 => by
      refine Activity.mem_activeThroughout.1 hwA j ?_ ?_
      · have : x.time j ≤ x.time k := htime hj2
        linarith [hkT.2]
      · have : x.time j ≤ x.time (j + 1) := htime (Nat.le_succ j)
        linarith)
  exact (stepFrame_of_compat_fin M F U) S A x R C.E X W s' w hXW hkl hlt hcf hWT hkv
    ((tick_step_le_of_le M F) C.E hkl hkv hcv) hr1 hf1 hfin

/-- **The round's fifth clause.** The next opening's proposer `q` (honest at the support cutoff of
slot `s''`) saved a confirmation `D` of slot `s'' − 2`, its root in the state its tick to the start of slot
`s''` starts from is `D` or an ancestor of `D` (`rootChain_at`), and its frame there has a viable
head that is `D` or a descendant of `D` (`frameP_of_conf`), B6's context at the window ending at
slot `s''`. Read at the proposer's tick input.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `hs''`: the end of the range read is the next honest round opening slot's
  first slot.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: the next honest round opening slot's proposer saved a confirmation `D` of slot
`s'' − 2`, with its root `D` or an ancestor of `D` and a viable head that is `D` or a descendant of
`D`. -/
theorem clause5 (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hs'' : rs (i + 1) * S.C.R = s'') :
    ∃ D : Block V,
      (∃ v ∈ Hon M S A x (s'' - 2),
        (x.tickOutput v (M.supportCutoff S.C (s'' - 1))).savedConfirmation (s'' - 2) =
          some D) ∧
      (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).fc_root.AncestorEq D ∧
      ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).tree,
        W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).viable_heads ∧
        D.AncestorEq W := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hsR := C.sR
  have hR := S.C.R_ge_two
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hmx := le_max_left (Δ S) Δs
  -- B6's bundle at the window ending at slot `s''`, with roots until `ΔClockBehind` after its support cutoff
  have C6 := (C.b6_at M F R U) (show s₀ + 1 ≤ s'' by omega) (le_refl s'') C.hRoots le_rfl
  have hcE : M.supportCutoff S.C s'' ≤ tAwakeEnd := C6.tEnd M F
  have hqH : S.P.proposer s'' ∉ A.corruptedAtTime x (M.supportCutoff S.C s'') := by
    have h := C.hSeq.honest (i + 1) C.hi
    rw [hs''] at h
    exact h
  have hsync := (C6.syncStart M F U) (show s'' - S.C.k - 1 ≤ s'' by omega)
  have hsyncK := (C6.syncStart M F U) (le_refl (s'' - S.C.k - 1))
  obtain ⟨σ, hσ⟩ : ∃ σ, s'' = σ + 2 := ⟨s'' - 2, by omega⟩
  subst hσ
  rw [show σ + 2 - 2 = σ by omega, show σ + 2 - 1 = σ + 1 by omega]
  have hq : S.P.proposer (σ + 2) ∈ Hon M S A x (σ + 1) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hqH⟩
  have hq' : S.P.proposer (σ + 2) ∈ roundMembers M S A x (σ + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (σ + 1) (σ + 2) tAwakeEnd R C.E (Nat.le_succ _) hcE).1 hq
  have hsc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hvσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hss2 : M.slotStart S.C (σ + 2) = M.slotStart S.C (σ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (σ + 1)]
    exact Nat.mul_succ _ _
  have hss1 : M.slotStart S.C (σ + 1) = M.slotStart S.C σ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hsc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hvK := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 2 - S.C.k - 1)
  have hμK := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (show σ + 2 - S.C.k - 1 ≤ σ by omega)
  -- the root: `rootChain_at` at the proposer's tick to the start of slot `σ + 2`
  obtain ⟨D, hD, hRD⟩ := (C6.rootChain_at M F R U Fx) rfl (S.P.proposer (σ + 2)) hq
    (M.slotStart S.C (σ + 2)) (by omega) (by omega)
  rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hRD
  -- the proposer's tick to the start of slot `σ + 2`, and to the window's start value
  have hqAH := (C6.awakeHonest M F R C.E) (S.P.proposer (σ + 2)) (t₁ := tGAT) (b := M.supportCutoff S.C (σ + 2)) le_rfl hcE hqH
  have hkQ := (tickStep_spec M) x R C.E (t := M.slotStart S.C (σ + 2)) (v := S.P.proposer (σ + 2)) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ + 2) : ℕ) : ℝ) := by
            exact_mod_cast (show tGAT + Δ S ≤ M.slotStart S.C (σ + 2) by omega)
          linarith)
      (by have : ((M.slotStart S.C (σ + 2) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C (σ + 2) + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
          linarith) hqAH)
  have hTt : x.tickInput (S.P.proposer (σ + 2)) (M.slotStart S.C (σ + 2)) =
      x.st (x.tickStep (S.P.proposer (σ + 2)) (M.slotStart S.C (σ + 2))) (S.P.proposer (σ + 2)) := by
    unfold Trace.tickInput
    rfl
  obtain ⟨kq, hkqdef⟩ : ∃ kq, kq = x.tickStep (S.P.proposer (σ + 2)) (M.slotStart S.C (σ + 2)) := ⟨_, rfl⟩
  rw [← hkqdef] at hTt hkQ
  obtain ⟨hkql, hkq1, -⟩ := hkQ
  have hqkq : S.P.proposer (σ + 2) ∉ A.corrupted kq := C.E.not_mem_corrupted_of_tick hkql
  have hkqT : x.time kq ≤ (((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + ΔClockBehind) :=
    (tick_time_le_of_clock_le M F) x C.E (c₀ := M.supportCutoff S.C (σ + 2)) le_rfl kq _ _ hkql (by omega)
  have hkqE : x.time kq ≤ (tAwakeEnd : ℝ) :=
    (tick_time_le_of_clock_le M F) x C.E (c₀ := M.slotStart S.C (σ + 2))
      (by have : ((M.slotStart S.C (σ + 2) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C (σ + 2) + Δ S ≤ tAwakeEnd by omega)
          linarith) kq _ _ hkql le_rfl
  have hk0 : x.lbl (x.tickStep (S.P.proposer (σ + 2)) (M.voteTime S.C (σ + 2 - S.C.k - 1))) =
      Event.tick (S.P.proposer (σ + 2)) (M.voteTime S.C (σ + 2 - S.C.k - 1)) := by
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (σ + 2 - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (σ + 2 - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (σ + 2 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (σ + 2 - S.C.k - 1) + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
    exact ((tickStep_spec M) x R C.E (t := M.voteTime S.C (σ + 2 - S.C.k - 1)) (v := S.P.proposer (σ + 2)) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hqAH)).1
  -- the frame: `frameP_of_conf_st` at the proposer's tick step, with roots until `ΔClockBehind` after `cut(σ + 2)`
  have hb2 : M.voteTime S.C σ + 2 * Δ S ≤ M.supportCutoff S.C (σ + 2) := by omega
  have hkqb : ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) ≤ x.time kq := by
    have : ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + 2 * Δ S + Δ S ≤ M.slotStart S.C (σ + 2) by omega)
    linarith
  have hi₀ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ kq :=
    ((stepBefore_lt_of_le_time M) x R C.E (by omega) hkqb).le
  have hk0b : x.tickStep (S.P.proposer (σ + 2)) (M.voteTime S.C (σ + 2 - S.C.k - 1)) <
      x.stepBefore (M.voteTime S.C σ + 2 * Δ S) := by
    refine (lt_stepBefore_of_not_other M) x R C.E (by rw [hk0]; simp) ?_
    have h := (C.E.tick_active _ _ _ hk0).2.2
    have : ((M.voteTime S.C (σ + 2 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (σ + 2 - S.C.k - 1) + Δ S ≤ M.voteTime S.C σ + 2 * Δ S by omega)
    linarith
  obtain ⟨W, hWt, hWv, hDW⟩ := C6.frameP_of_conf_st M F R U Fx (σ := σ) (by omega) le_rfl
    (S.P.proposer (σ + 2)) hq' D D hD (ancestorEq_refl D) (S.P.proposer (σ + 2)) (M.voteTime S.C σ + 2 * Δ S) le_rfl hb2
    ((not_mem_corruptedAtTime_of_le M) x R C.E hb2 hqH) kq hkqE hi₀ hqkq
    (fun j hj hjk => (C6.noChange M F R C.E) (S.P.proposer (σ + 2)) hk0 hkql (by omega) j (by omega) hjk) C.hRoots hkqT
  rw [hTt] at hRD ⊢
  exact ⟨D, ⟨_, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (not_mem_corruptedAtTime_of_le M) x R C.E
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ (σ + 1))) hqH⟩, hD⟩,
    hRD, W, hWt, hWv, hDW⟩

/-- **The round is quiet relative to its own confirmations.** The five clauses, when the end of the
range read is the next honest round opening slot's first slot (`hs''`).

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle; `B`: the proposal.

Read aloud: the round of honest round opening slot `i` is quiet relative to its own confirmations.
-/
theorem quiet (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hs'' : rs (i + 1) * S.C.R = s'') (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) :
    QuietRoundOnConfirmations M S A x (Hon M S A x) B (s₀ + 1) s'' :=
  ⟨(C.clause1 M F R E U Fx) B hB, (C.clause2_tick M F R E U Fx) B hB, (C.clause3 M F R E U Fx) B hB, (C.clause4 M F R E U Fx), (C.clause5 M F R E U Fx) hs''⟩

end QuietCtxUpTo

/-- The context `QuietCtx` of the honest round opening slot `i` with `s₀ := rs i * R − 1` and the
end `s''` of the range read, from the hypotheses the climb's steps state: `s''` at least one round
after `rs i * R` and at most `r * R`, no fork-choice change to before its support cutoff. The
climb's steps take `s'' := rs (i + 1) * R` (`opening_round_step` for `hsR`); the honest round
opening slot whose round holds `r * R` takes `s'' := r * R`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- the others as in `spoiled_near_fork_choice_change_cutoff`; `s''`: the end of the range read.

Roots name blocks until `ΔClockBehind` after `M.supportCutoff S.C s''`, where the members' ticks to it end: the end of the range the context carries.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of its roots
`hRoots`; every delivery its proof reads is due by then.

Read aloud: the hypotheses of the climb's steps give the bundle `QuietCtx` of honest round opening
slot `i`. -/
theorem quietCtx_of_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ) {s'' : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s'')) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s''))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until `ΔClockBehind` after the support cutoff of slot `s''`, where the members' ticks to it end
    (hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j) :
    rs i * S.C.R = rs i * S.C.R - 1 + 1 ∧
    QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs (rs i * S.C.R - 1) s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet := by
  have hs1 : rs i * S.C.R = rs i * S.C.R - 1 + 1 := by
    have hk := S.C.k_ge_two
    have h0 : rs 0 * S.C.R ≤ rs i * S.C.R := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]
      · exact Nat.mul_le_mul_right _ (le_of_lt (r_lt_of_lt_of_mono rs m hSeq.mono 0 i h (le_of_lt hi)))
    have hw := (GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m
      tGAT tAwakeEnd (rs i * S.C.R) hSeq h0
    omega
  refine ⟨hs1, ?_⟩
  exact
    { E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs,
      hRoots := hRoots, hParent := hParent, hGST := hGST, hThird := hThird, hAwake := hAwake,
      hActive := hActive, hCommittees := hCommittees, hEnd := hEnd, hSeq := hSeq, hi := hi, hs := hs1,
      sR := by rw [← hs1]; exact hsR, hir := hir, hNoCol := hNoCol,
      hNo := by rw [← hs1]; exact hNo, htime := fun _ _ h => R.time_mono h }

namespace QuietCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- **A quiet round's proposal is attested at its action time, or its height was attested
before.** With the round's base
(`WinCtx.base`, the second clause giving
the roots at the action time), a member's update at the action time saves the proposal `B` with `B`
among its fast blocks, its live locks on `B`'s chain; so the member attests at `B`'s height at its
tick then, or its record already sent an attestation at that height, at an earlier tick
(`lem61_honest_validator_attests_frame`, `record_content_sent`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `B`: the proposal; `H₂`: a height below `B`'s.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`.

Read aloud: when the proposal is higher than `H₂`, an honest validator attests higher than `H₂` by
the action time of slot `s₀ + 1`. -/
theorem attests_above (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (B : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) (H₂ : ℕ) (hBh : H₂ < (M.chainStateOf S.C B).h)
    (tH : ℕ) (htH : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tH) (htHE : tH ≤ tAwakeEnd) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ M.supportCutoff S.C (s₀ + 1 + 1) ∧
      HonestAttestationAt M S A x t₀ v a ∧ H₂ < a.h ∧ v ∉ A.corruptedAtTime x tH := by
  have hSkew := C.hSkew
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hsR := C.sR
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEnd := (C.cut_end M F)
  have hc23 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₀ + 1 + 1 + 1 ≤ s'' by omega)
  have hc2s := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ tAwakeEnd := by omega
  have hcl2 := (C.clause2_tick M F R E U Fx) B hB
  obtain ⟨hHeld, hBase, hUpd⟩ := ((C.toWin M F).base M F R E U Fx) C.hNoCol B hB
    (fun v hv => ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F)
      S A x R E _ v) (hcl2 v hv).1)
  have hA2 : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1 + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  -- a validator honest through `tH`: fewer than a third are ever in the adversary set up to `tAwakeEnd`
  obtain ⟨v, hvT⟩ : ∃ v : V, A.HonestThroughTime x tH v := by
    by_contra hall
    have hall' : ∀ w ∈ (Finset.univ : Finset V),
        ∃ i : ℕ, x.time i ≤ tH ∧ w ∈ A.corrupted i := by
      intro w _
      by_contra hn
      exact hall ⟨w, fun i hi hadv => hn ⟨i, hi, hadv⟩⟩
    have h3 := ((GoldilocksCorrectness.Record.Proofs.Executions.adversaryFewerThanThirdUntil_of_le M F) htHE C.hThird) Finset.univ hall'
    rw [Finset.card_univ] at h3
    unfold validator_count at h3
    omega
  -- it is a member of the slot: honest at the support cutoff of slot `s₀ + 2`
  have hvb : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hvT i (le_trans hi (by exact_mod_cast htH))
  have hvH : v ∈ Hon M S A x (s₀ + 1) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvb⟩
  obtain ⟨iB, hlB, hsentB⟩ := hB
  obtain ⟨hBslot, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_parent_walk_end M F U) S A x R E s₀ iB B _ hlB hsentB
  have hdw1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1) hA2
  -- `v` is an updater of slot `s₀ + 1`: it ticks to the support cutoff of slot `s₀ + 2`
  have hvU : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₀ + 1 + 1)) (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    (C.hActive (s₀ + 1) (by omega) (by omega) v hvb).2
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hvU
  have hvkc : v ∉ A.corrupted kc := E.not_mem_corrupted_of_tick hkc
  have hkcT := ((time_of_lbl_tick M) x R E hkc).1
  have hkcS : x.tickStep v (M.supportCutoff S.C (s₀ + 1 + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  -- the outcome of that tick, from a state awake since at most the duty window's start
  obtain ⟨n', sent, hUp, hAw, -⟩ := (update_state_of_tick M F U) S A x R (s₀ + 1) v E hkc
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hvU
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (s₀ + 1 + 1)))
  obtain ⟨hS, hF⟩ := hUpd v hvH n' sent hUp hAw
  have hLk := (GoldilocksCorrectness.Record.Proofs.Executions.update_lock_entries_ancestorEq M F U) S A x R (s₀ + 1) B v E hSkew hvU n' sent hUp hAw hS hBslot
    (hBase.2.1 v hvH)
  -- `B` is held at the tick to the vote time of slot `s₀ + 1`, an earlier tick of `v`
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  obtain ⟨hvt1, hct1, -, hst1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  obtain ⟨-, hct2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hvA := (mem_activeThroughout_of_hAwake_honest_at M F) R E C.hAwake le_rfl
    (by omega : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd) hvb
  have hkv := (tickStep_spec M) x R E (t := M.voteTime S.C (s₀ + 1)) (v := v) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by
        have : (tGAT : ℝ) + Δ S ≤ ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s₀ + 1) by
            have : tGAT ≤ tGAT + 4 * Δ S * (S.C.k + 2) := Nat.le_add_right _ _
            omega)
        linarith [hSkew])
      (by
        have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
        linarith [hSkew]) hvA)
  have hkvkc : x.tickStep v (M.voteTime S.C (s₀ + 1)) ≤ kc := by
    by_contra hc
    push Not at hc
    have := E.clock_mono kc _ v _ _ hc (E.not_mem_corrupted_of_tick hkv.1) (Or.inl hkc) (Or.inl hkv.1)
    omega
  have hBin : B ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1 + 1))).tree := by
    unfold Trace.tickInput
    rw [hkcS]
    exact ((grows_of_le M F) x R E v hkvkc).1 (hHeld v hvH)
  -- the lock box at that tick input
  have hLockBox := (lockBox_of_frame_tick M F Fx) S A x R E _ v B
    (C.hThird.mono (by
      rw [hkcS]
      have : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEs2
      linarith [hkcT.2, hSkew])) (hcl2 v hvH).1 (hcl2 v hvH).2
  rcases (GoldilocksCorrectness.Record.Proofs.Executions.lem61_honest_validator_attests_frame M F U) S A x R (rs i) (s₀ + 1) B v _ _ E
      C.hs.symm hvU n' sent hUp hAw hS hF hLk ⟨rfl, rfl⟩ (hcl2 v hvH).1 (hcl2 v hvH).2 hBin
      hLockBox with ⟨i', a, hl, hsent, -, hah, -⟩ | ⟨b, hb, hbh, -⟩
  · exact ⟨_, v, a, le_rfl, ⟨i', hl, hsent⟩, by rw [hah]; exact hBh,
      Activity.not_mem_corruptedAtTime.2 fun i hi => hvT i hi⟩
  · -- the attestation of `b` went out at an earlier tick of `v`, to a clock value at most the cutoff
    have hb' : b ∈ (x.st kc v).sentAttestations := by
      have h := hb
      unfold Trace.tickInput at h
      rwa [hkcS] at h
    obtain ⟨j, t', a, hjkc, hl, -, hsent, -, hac, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Executions.record_content_sent_step M F) S A x R E v kc b hb'
    have ht' : t' ≤ M.supportCutoff S.C (s₀ + 1 + 1) :=
      E.clock_mono j kc v _ _ hjkc hvkc (Or.inl hl) (Or.inl hkc)
    have hah : a.h = b.h := by
      rw [← hac]
      rfl
    exact ⟨t', v, a, ht', ⟨j, hl, hsent⟩, by rw [hah, hbh]; exact hBh,
      Activity.not_mem_corruptedAtTime.2 fun i hi => hvT i hi⟩

end QuietCtxUpTo

/-- **B11 over an honesty time `tH`: a quiet opening above the threshold attests above it, by a
validator honest at `tH`.** `quiet_top_gives_attestation_cutoff_upTo` with the attester chosen outside the adversary set up to any
time `tH` from the round's action time to `tAwakeEnd` (`attests_above` over `tH`).

The variables: as for `quiet_top_gives_attestation_cutoff_upTo`; `tH`: the time the attester's honesty is read at.

Read aloud: a quiet honest round opening slot whose proposal is higher than `H₂` has an
attestation higher than `H₂` by the round's action time, sent by a validator still honest at `tH`. -/
theorem quiet_top_gives_attestation_cutoff_upTo_at (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r m i H₂ s'' : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s'')) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s''))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until `ΔClockBehind` after the support cutoff of slot `s''`, where the members' ticks to it end
    (hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB : ProposalAt M S x (rs i * S.C.R) B) (hBh : H₂ < (M.chainStateOf S.C B).h)
    (tH : ℕ) (htH : aR M S (rs i) ≤ tH) (htHE : tH ≤ tAwakeEnd) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ aR M S (rs i) ∧
      HonestAttestationAt M S A x t₀ v a ∧ H₂ < a.h ∧ v ∉ A.corruptedAtTime x tH := by
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hGST hThird hAwake hActive hCommittees hEnd hSeq hi hsR hir hNoCol hNo
  rw [hs1] at hB
  obtain ⟨t₀, v, a, ht₀, hA, ha, hvH⟩ := (C.attests_above M F R E U Fx) B hB H₂ hBh tH
    (by unfold aR at htH; rw [← hs1]; exact htH) htHE
  refine ⟨t₀, v, a, ?_, hA, ha, hvH⟩
  unfold aR
  rw [← hs1] at ht₀
  exact ht₀

/-- **B11 restated, on a copy: a quiet opening above the threshold attests above it.** The proof;
the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: `quietCtx_of`, then
`QuietCtx.attests_above` at the action
time `aR M S (rs i)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `r`: the round of the action time the climb ends at; `m`: the index of the last honest round opening slot; `i`:
  the index of an honest round opening slot; `H₂`: the threshold; `rs`: the rounds of the honest round opening slots; `B`: the proposal at the honest round opening slot.

Roots name blocks until `ΔClockBehind` after `M.supportCutoff S.C s''`, where the members' ticks to it end: the end of the range the context `QuietCtx`
carries (`quietCtx_of`).

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of its roots
`hRoots`; every delivery its proof reads is due by then.

Read aloud: a quiet honest round opening slot whose proposal is higher than `H₂` has an honest
attestation higher than `H₂` by the round's action time. -/
theorem quiet_top_gives_attestation_cutoff_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r m i H₂ s'' : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s'')) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s''))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until `ΔClockBehind` after the support cutoff of slot `s''`, where the members' ticks to it end
    (hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB : ProposalAt M S x (rs i * S.C.R) B) (hBh : H₂ < (M.chainStateOf S.C B).h) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ aR M S (rs i) ∧
      HonestAttestationAt M S A x t₀ v a ∧ H₂ < a.h := by
  have hti : aR M S (rs i) ≤ tAwakeEnd := le_trans (by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  obtain ⟨t₀, v, a, ht₀, hA, ha, -⟩ := (quiet_top_gives_attestation_cutoff_upTo_at M F U Fx) S A x R GST tGAT tAwakeEnd r m i H₂ s''
    rs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive hCommittees hEnd hSeq hi hsR hir hNoCol hNo hB hBh
    (aR M S (rs i)) le_rfl hti
  exact ⟨t₀, v, a, ht₀, hA, ha⟩

namespace QuietCtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r m i : ℕ} {rs : ℕ → ℕ} {s₀ s'' : ℕ}

/-- **Lemma 89r at an opening with no fork-choice change.** For the opening's proposal `B` and the
next opening's proposal `B'`: `B'` is on `B`'s chain and raises the height or carries the progress
quorum within `δt` of `B`'s entry, and the rest of `lem89r_quiet_round`'s conclusion, for the
window's family (`WinCtx.fam`); its
collision case is excluded by `hNoCol`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `C`: the context; `hs''`: the end of the range read is the next honest round opening slot's
  first slot; `B`, `B'`: the two proposals.

Restated with the delivery premises up to `M.supportCutoff S.C s''`: the bound of the bundle
`QuietCtxUpTo`, for the votes; the attestations (`hSyncF`, `hCatchF`) up to `M.slotStart S.C s''`,
the bound `lem89r_quiet_round_upTo` reads them at.

Read aloud: the next honest round opening slot's proposal descends from the proposal and raises the
height or carries the progress quorum in time, and every member saves the proposal at the action
time. -/
theorem round89r (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i rs s₀ s'' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hs'' : rs (i + 1) * S.C.R = s'') (B B' : Block V)
    (hB : ProposalAt M S x (s₀ + 1) B) (hB' : ProposalAt M S x s'' B')
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C s'')) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C s''))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- the members of the opening's first slot are active through the attestations' sync delay after the later of its
    -- duty window's start and `GST`
    (hHoldF : ∀ v ∈ Hon M S A x (s₀ + 1), v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (s₀ + 1)) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C (s₀ + 1)) GST : ℕ) : ℝ) + Δs_F)) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (M.chainStateOf S.C B').progress)) ∧
    (∀ v ∈ Hon M S A x (s₀ + 1),
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1 + 1))).savedConfirmation (s₀ + 1) =
        some B) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hsR := C.sR
  have hR := S.C.R_ge_two
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hEnd := (C.cut_end M F)
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hanc := hw0.2
  rw [anchorCW_eq] at hanc
  have hμs := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ by omega)
  have hGSTt := C.hGST
  have hpH : S.P.proposer (s₀ + 1) ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := by
    have h := C.hSeq.honest i (le_of_lt C.hi)
    rw [C.hs] at h
    exact h
  have hpAH := C.awakeHonest M F R E _ (t₁ := tGAT) le_rfl
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd) hpH
  have hqH : S.P.proposer s'' ∉ A.corruptedAtTime x (M.supportCutoff S.C s'') := by
    have h := C.hSeq.honest (i + 1) C.hi
    rw [hs''] at h
    exact h
  obtain ⟨hChain, hLocks, hAnchor, -, hFrameP⟩ := (C.toWin M F).fam M F R E U Fx
  have hsy0 := ((C.toWin M F).b6 M F U).syncStart M F U (σ := s₀) (by omega)
  have hsy1 := ((C.toWin M F).b6 M F U).syncStart M F U (σ := s₀ + 1) (by omega)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hmx1 := le_max_left (Δ S) Δs
  have hmemD : ∀ a b : ℕ, a ≤ b → b ≤ s'' → ∀ u ∈ roundMembers M S A x b,
      u ∈ roundMembers M S A x a := fun a b hab hb u hu =>
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A a b tAwakeEnd R E hab
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hb) hEnd)).1 hu
  have hle89 : M.supportCutoff S.C (s'' - 1) ≤ M.supportCutoff S.C s'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have E89 : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s'' - 1)) :=
    GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy.restrict C.E fun _ _ _ h => by
      obtain ⟨h1, rfl⟩ := GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.1 h
      exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨le_trans h1 (by exact_mod_cast hle89), rfl⟩
  -- every member of a slot `s'` of the range is active from the slot's duty window's start to the support cutoff of slot
  -- `s' + 1`, an honest active validator and an updater of slot `s'` (the bundle's `hActive`;)
  have hMemWin : ∀ s', s₀ ≤ s' → s' < s'' → ∀ v ∈ Hon M S A x s',
      v ∈ A.activeThroughout x (M.dutyWindowStart S.C s') (M.supportCutoff S.C (s' + 1)) := by
    intro s' h1 h2 v hv
    have hA : anchorCW S tGAT ≤ M.slotStart S.C (s' + 1) :=
      le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s' hA
    exact Activity.mem_activeThroughout_of_le (by first | (norm_cast; omega) | norm_cast) (by first | (norm_cast; omega) | norm_cast) (C.awakeHonest M F R E v (t₁ := tGAT) le_rfl
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd) (Finset.mem_sdiff.1 hv).2)
  --: every member of a slot `s'` of the range ticks to a clock value `b` whose real time plus the behind bound
  -- is at most the support cutoff of slot `s' + 1`, active up to that tick from its own tick to a clock value at most the
  -- protocol's duty window start of slot `s'`: its window from `tGAT` opens more than the ahead bound before that start
  have hMemRd : ∀ s', s₀ ≤ s' → s' < s'' → ∀ v ∈ Hon M S A x s', ∀ b : ℕ, 1 ≤ b →
      duty_window_start S.C s' ≤ (b : ℤ) → (b : ℝ) + ΔClockBehind ≤ ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) →
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') b := by
    intro s' h1 h2 v hv b hb1 hb hbB
    have hA : anchorCW S tGAT ≤ M.slotStart S.C (s' + 1) :=
      le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    have hd := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s' hA
    have hdr := (duty_window_start_real_of_pos M F U) S s' (by omega)
    have hA0 := C.E.ahead_nonneg
    have hB0 := C.E.behind_nonneg
    have hsk := C.hSkew
    have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C s' : ℕ) : ℝ) := by exact_mod_cast hd
    push_cast at hdR
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R C.E hb1 hb ?_
    refine Activity.mem_activeThroughout_of_le ?_ hbB (C.awakeHonest M F R E v (t₁ := tGAT) le_rfl
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd) (Finset.mem_sdiff.1 hv).2)
    rw [hdr]
    linarith
  have hMemAct : ∀ s', s₀ ≤ s' → s' < s'' → ∀ v ∈ Hon M S A x s',
      v ∈ honestActiveAt M S A x s' ∧ v ∈ updaterAt M S A x s' := by
    intro s' h1 h2 v hv
    have hA : anchorCW S tGAT ≤ M.slotStart S.C (s' + 1) :=
      le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s' hA
    exact C.hActive s' (by omega)
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd)
      v (Finset.mem_sdiff.1 hv).2
  have h89 := (GoldilocksCorrectness.Record.Proofs.Executions.lem89r_quiet_round_upTo M F U Fx) S A x R GST (rs i) (s₀ + 1) s'' (Hon M S A x)
    (WinFam M S A x s₀) B B' (S.P.proposer (s₀ + 1)) (S.P.proposer s'') E89 C.hNet C.hSkew C.hRedeliver (C.Sy.mono hle89) C.hΔs E_F hNet_F hSkew_F Sy_F hΔs_F
    --: roots until the real time of the support cutoff of slot `s'' − 1`, from the bundle's roots
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by
      have hB0 := C.E.behind_nonneg
      have hm : ((M.supportCutoff S.C (s'' - 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
        exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.sub_le s'' 1)
      linarith) C.hRoots)
    ((per_tick_roots_of_roots_until M F) x C.E ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_add_of_nonneg_right C.E.behind_nonneg) C.hRoots) (by
      have hB0 := C.E.behind_nonneg
      have hs1 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'')
      have hs0 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s'' - 1))
      have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s''
      have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s'' - 1)
      have hw1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s''
      have hw0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s'' - 1)
      have hsm : M.slotStart S.C (s'' - 1) + 4 * Δ S = M.slotStart S.C s'' := by
        rw [hs1, hs0, show s'' = s'' - 1 + 1 by omega, Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
      have hn : M.supportCutoff S.C (s'' - 1) + Δ S ≤ M.supportCutoff S.C s'' := by omega
      have hnR : ((M.supportCutoff S.C (s'' - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
        exact_mod_cast hn
      have hsk := C.hSkew
      have hA0 := C.E.ahead_nonneg
      linarith)) C.hParent
     C.hs.symm (by omega)
    ((GoldilocksCorrectness.Record.Proofs.Routines.delivery_of_round M.toSlotLayout F.sched) S C.sR)
    (by rw [Nat.add_sub_cancel]; omega)
    (by
      --: the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
      have hdel := (GoldilocksCorrectness.Record.Proofs.Routines.delivery_of_round M.toSlotLayout F.sched) S C.sR
      have hanc' := hanc
      rw [Nat.mul_add] at hanc'
      have hs0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ ≤ s'' by omega)
      have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
      have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
      have hss2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 ≤ s₀ + 1 + 1 by omega)
      have hΔsF : Δs_F ≤ Δ_F S ∨ Δs_F + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
        have hA0 := C.E.ahead_nonneg
        have hB0 := C.E.behind_nonneg
        rcases hΔs_F with h | h
        · left
          exact_mod_cast (show (Δs_F : ℝ) ≤ Δ_F S by linarith)
        · right
          exact_mod_cast (show ((Δs_F + 3 * Δ S : ℕ) : ℝ) ≤ ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
      rcases max_choice (Δ_F S) Δs_F with hm | hm <;> rw [hm] <;> omega)
    --: the bound up to each member's own tick to the support cutoff of slot `s₀ + 2`, from the bound up to
    -- `tAwakeEnd`: that tick is at a real time at most the behind bound after the cutoff, before `tAwakeEnd`
    (fun v _ => (adversaryFewerThanThirdUntil_tickStep M F) x R C.E v _ (by
      have h3 : M.slotStart S.C (s₀ + 1 + 1 + 1) = M.slotStart S.C (s₀ + 1 + 1) + 4 * Δ S := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
          Nat.mul_one]
      have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
      have hc3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1 + 1)
      have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
      have hv3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1 + 1)
      have hE3 : M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ tAwakeEnd :=
        le_trans (by omega) (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show s₀ + 1 + 1 + 1 ≤ s'' by omega)) hEnd)
      have hE3R : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hE3
      have hA0 := C.E.ahead_nonneg
      have hsk := C.hSkew
      linarith) C.hThird)
    (fun s' h1 h2 => hmemD (s' + 1) (s' + 1 + 1) (Nat.le_succ _) (by omega))
    --: the members of every slot from `s₀` to `s'' − 1` are honest active validators of it (the bundle's
    -- `hActive`)
    (fun s' h1 h2 v hv => (hMemAct s' (by omega) (by omega) v hv).1)
    --: the holder clause of the first slot's members, from their window to the support cutoff of slot `s₀ + 2`
    (fun w hw => (holder42_of_dev_window M F U) S A x C.E.ahead_nonneg C.E.behind_nonneg C.hΔs
      (le_trans (by omega : max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
        ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)))
      (hMemWin (s₀ + 1) (by omega) (by omega) w hw))
    --: the members' view-freeze holder row, from their window to the support cutoff of slot `s₀ + 2`
    (fun w hw => (holderV_of_dev_window M F U) S A x C.E.ahead_nonneg C.E.behind_nonneg C.hΔs
      (by
        have hvf := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (s₀ + 1)
        have := (le_trans (by omega : max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
          ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
            (show s₀ ≤ s₀ + 1 by omega)))
        omega)
      (hMemWin (s₀ + 1) (by omega) (by omega) w hw))
    --: the members' holder row at the attestations' sync read time, a parameter
    hHoldF
    ((fun (t : ℕ) (Hn : Finset V) (hTh : A.AdversaryFewerThanThirdUntil x (validator_count V) t) (hSup : Finset.univ \ A.corruptedAtTime x t ⊆ Hn) => (show quorum V ≤ Hn.card by have h1 := Finset.card_le_card hSup; have h2 : 3 * (A.corruptedAtTime x t).card < validator_count V := hTh _ (fun v hv => by obtain ⟨i, hi, hc⟩ := Activity.mem_corruptedAtTime.1 hv; exact ⟨i, hi, hc⟩); rw [Finset.card_univ_sdiff] at h1; unfold quorum; unfold validator_count at *; omega)) tAwakeEnd _ C.hThird
      ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (s₀ + 1 + 1) (s₀ + 1 + 1) tAwakeEnd R E le_rfl hEs2).2)
    (by
      intro s' h1 h2
      have hA : anchorCW S tGAT ≤ M.slotStart S.C (s' + 1) :=
        le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
      exact (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x _ s' C.hCommittees hA
        (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd))
    --: `tStart := tGAT + Δ S`, more than both clock bounds before Lemma 12's read time of slot `s₀`
    (tGAT + Δ S)
    (by
      rw [Nat.add_sub_cancel]
      have hA0 := C.E.ahead_nonneg
      have hB0 := C.E.behind_nonneg
      have hsk := C.hSkew
      have hΔsC := C.hΔs
      have hcut : tGAT + 4 * Δ S * (S.C.k + 2) + 2 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
      have hcutR : ((tGAT : ℕ) : ℝ) + 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 2) + 2 * Δ S ≤
          ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hcut
      have hDk : (0 : ℝ) ≤ (Δ S : ℝ) * S.C.k := by positivity
      have hΔsR : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := by exact_mod_cast le_max_right (Δ S) Δs
      have hT0 : (0 : ℝ) ≤ (tGAT : ℝ) := by positivity
      have h1 : (tGAT : ℝ) + Δ S + ΔClockAhead + ΔClockBehind + 2 * Δ S <
          ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by nlinarith
      have h2 : (tGAT : ℝ) + Δ S + ΔClockAhead + ΔClockBehind + Δs <
          ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by nlinarith
      have hm : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
        have : ((max (2 * Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by
          push_cast
          exact max_le (by linarith) (by linarith)
        exact_mod_cast this
      rw [Nat.cast_sub hm]
      push_cast
      have := max_lt (show (2 * (Δ S : ℝ)) < (M.supportCutoff S.C s₀ : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
        ΔClockBehind by linarith) (show (Δs : ℝ) < (M.supportCutoff S.C s₀ : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
        ΔClockBehind by linarith)
      linarith)
    (by
      -- the proposer's reader to its tick to the start of slot `s₀ + 1`, from its window from `tGAT`
      have hA0 := C.E.ahead_nonneg
      have hB0 := C.E.behind_nonneg
      have hsk := C.hSkew
      have hc2 : M.slotStart S.C (s₀ + 1) + 2 * Δ S = M.supportCutoff S.C (s₀ + 1) := by omega
      have hc2R : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + 2 * Δ S = ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hc2
      have hle : tGAT + Δ S ≤ M.slotStart S.C (s₀ + 1) := by omega
      refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R C.E (by omega) (by exact_mod_cast hle) ?_
      refine Activity.mem_activeThroughout_of_le ?_ ?_ hpAH
      · push_cast; linarith
      · linarith)
    (by
      -- the proposer's holder row at the start of slot `s₀ + 1`, inside its window from `tGAT`
      have h : tGAT + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := by omega
      have hu : M.slotStart S.C (s₀ + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s₀ + 1) := by
        have := le_max_right (Δ S) Δs
        omega
      have hl : tGAT ≤ M.slotStart S.C (s₀ + 1) - max (Δ S) Δs := by omega
      exact Activity.mem_activeThroughout_of_le (by exact_mod_cast hl) (by exact_mod_cast hu) hpAH)
    --: the proposer at each member's tick to the vote time of slot `s₀ + 1`, before the cutoff where it is
    -- honest
    (fun w _ => (proposer_honest_at_member_tick M F U) R C.E C.hSkew hpH)
    (by
      show S.P.proposer s'' ∈ roundMembers M S A x (s'' - 1 + 1)
      rw [show s'' - 1 + 1 = s'' by omega]
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hqH⟩)
    rfl rfl
    (by
      --: `q`'s receiver row, inside its window from `tGAT` to the support cutoff of slot `s''`: the sync
      -- read time is after `tGAT`, and `q`'s tick to the start of slot `s''` is at most the behind bound after it
      intro i' h1 h2
      have hqAH := C.awakeHonest M F R C.E (S.P.proposer s'') (t₁ := tGAT) le_rfl hEnd hqH
      have hA : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1 + 1) :=
        le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
      have hd := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
        (s₀ + 1) hA
      have hdR : ((tGAT : ℕ) : ℝ) ≤ ((max (M.dutyWindowStart S.C (s₀ + 1)) GST : ℕ) : ℝ) := by
        exact_mod_cast le_trans (by omega : tGAT ≤ M.dutyWindowStart S.C (s₀ + 1)) (le_max_left _ _)
      have ht := (time_tickStep_le_add_behind M F) x R C.E (S.P.proposer s'') (M.slotStart S.C s'')
      have hmono := R.time_mono h2
      have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s''
      have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s''
      have h9 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s''
      have hle : M.slotStart S.C s'' + Δ S ≤ M.supportCutoff S.C s'' := by omega
      have hleR : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by exact_mod_cast hle
      have hA0 := C.E.ahead_nonneg
      have hsk := C.hSkew
      exact Activity.mem_active_of_mem_activeThroughout_of_time (fun _ _ h => R.time_mono h) hqAH
        (le_trans hdR h1) (by linarith))
    hB hB' ((C.quiet M F R E U Fx) hs'' B hB) (by rw [Nat.add_sub_cancel]; exact hChain)
    (by rw [Nat.add_sub_cancel]; exact hLocks) hAnchor hFrameP
  rcases h89 with hcol | ⟨hBB', hrise, -, hsave, -, -⟩
  · exfalso
    apply C.hNoCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M x)]
    refine ⟨i, le_of_lt C.hi, B, ?_, ?_⟩
    · rw [C.hs]
      exact hB
    · rw [C.hs]
      exact hcol
  · exact ⟨hBB', hrise, hsave⟩

end QuietCtxUpTo

end GoldilocksCorrectness.Record.Proofs.Executions

