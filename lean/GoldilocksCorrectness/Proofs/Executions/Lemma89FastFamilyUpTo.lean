module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastBaseUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89fUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma32UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma42UpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatementsUpTo

@[expose] public section

/-!
# `Lemma89FastFamily.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastFamily.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `PartAHyps`, `window`, `dws`, `member`, `member1`, `member0`, `gst`, `source_L`, `source_conf`,
  `source_lock`, `sources_compatible_le`, `sources_compatible`, `cert_source`,
  `source_inHonestTreeBy`, `source_held`, `L_held_v`, `L_held`, `F_compat`, `L_tall`,
  `root_compat`, `tall_entry`, `viable_candidate`, `frame_source_at`, `stepFrame_source`,
  `old_lock_compat`, `base_locks`, `members_sets`, `committee`, `base_source`, `step_source`,
  `lineInv_all`, `lineInv_upto`, `source_later`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_le_voteTime dutyWindowStart_mono dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart slotStart_mono supportCutoff_eq supportCutoff_lt
  supportCutoff_mono tGAT_le_slotStart t_lt_of_lt times_eq viewFreeze_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_height_mono
  compatible_of_ancestorEq_both compatible_symm' entry_eq_of_compatible)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_ancestorEq_of_tall floor_le_h_max
  mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq fg_contest_spec
  head_height_floor_of_not_contested is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (root_cases)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn CountedVotes
  ProgressCertOn JustificationCertOn FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `PartAHyps S Sched x GST tGAT tAwakeEnd r H₂ v L A'`: the hypotheses of A5 `fast_block_base`
but its bound on the phase's end.

Roots name blocks until `tAwakeEnd`: the phase's end; each kit theorem reads blocks held up to the
end time its own hypothesis `hEnd` bounds by `tAwakeEnd`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of its roots `hRoots`, the phase's end; each reader reads deliveries due by an end time its own hypothesis bounds by `tAwakeEnd`. -/
structure PartAHypsUpTo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V) (A' : ACState V) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tAwakeEnd
  hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tAwakeEnd
  hRoots : RootsNameBlocksUntil S Sched x tAwakeEnd
  hParent : ParentHeldAtDelivery S Sched x
  hOwner : VotesCastByOwner S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hGST : GST ≤ tGAT
  hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int)
  hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
    ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int)
  hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT)
  hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1)
  hOld : OldAttestationsAtMost S Sched x (aR S r) H₂
  hv : v ∉ Sched.adv ((aR S r : ℕ) : Int)
  hUpdate : update_confirmation S.C S.P
      (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
      (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A'
  hFast : L ∈ A'.fast_blocks
  hL : (chainStateOf S.C L).h = H₂ + 1

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- A validator honest at `t₀ ≤ tAwakeEnd` is awake and honest at every `t` from `tGAT` to `t₀`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem window (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {u : V} {t₀ : ℕ}
    (hu : u ∉ Sched.adv (t₀ : Int)) (h₀ : t₀ ≤ tAwakeEnd) :
    ∀ t : ℕ, tGAT ≤ t → t ≤ t₀ → u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
  intro t h1 h2
  have hn : u ∉ Sched.adv (t : Int) := fun h => hu (P.hMono _ _ (by exact_mod_cast h2) h)
  exact ⟨P.hAwake t h1 (le_trans h2 h₀) u hn, hn⟩

/-- The duty window of every slot from `r * R` on starts after `tGAT`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem dws (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R ≤ s) : tGAT + Δ S ≤ dutyWindowStart S s :=
  le_trans (dutyWindowStart_of_anchor S tGAT (r * S.C.R) P.hAnchor) (dutyWindowStart_mono S hs)

/-- A member of `Hon S Sched s`, `s ≥ r * R`, with the support cutoff of slot `s + 1` in the phase,
is awake and honest from `tGAT` to that cutoff.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem member (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ} {u : V}
    (hu : u ∈ Hon S Sched s) (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
  unfold Hon roundMembers at hu
  exact P.window (Finset.mem_sdiff.1 hu).2 hEnd

/-- A member of `Hon S Sched s`, `s ≥ r * R`, is awake and honest from the duty window's start of
slot `s + 1` to the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem member1 (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ} {u : V}
    (hs : r * S.C.R ≤ s) (hu : u ∈ Hon S Sched s) (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := fun t h1 h2 =>
  P.member hu hEnd t (by have := P.dws (show r * S.C.R ≤ s + 1 by omega); omega) h2

/-- A member of `Hon S Sched s`, `s ≥ r * R`, is awake and honest from the duty window's start of
slot `s` to the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem member0 (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ} {u : V}
    (hs : r * S.C.R ≤ s) (hu : u ∈ Hon S Sched s) (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := fun t h1 h2 =>
  P.member hu hEnd t (by have := P.dws hs; omega) h2

/-- `GST` is at most the duty window's start, the vote time and the support cutoff of every slot
from `r * R` on.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem gst (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R ≤ s) : GST ≤ dutyWindowStart S s ∧ GST ≤ voteTime S s ∧
      GST ≤ supportCutoff S s := by
  have h1 := P.dws hs
  have h2 := dutyWindowStart_le_voteTime S s
  have h3 := supportCutoff_eq S s
  have h4 := P.hGST
  omega

/-- The fast block `L` is a line source of slot `r * R`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem source_L (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    (hEnd : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd) :
    LineSource S Sched x r H₂ (r * S.C.R) L := by
  have hvH : v ∈ Hon S Sched (r * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, P.hv⟩
  have hU : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (r * S.C.R + 1)) v).A
        ((supportCutoff S (r * S.C.R + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (r * S.C.R + 1)) v).S)
      ((supportCutoff S (r * S.C.R + 1) : ℕ) : Int) (r * S.C.R + 1) = .ok A' := P.hUpdate
  obtain ⟨C', hC', hLC'⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved S.C S.P _ A' _ _
      (r * S.C.R + 1) L (Nat.le_add_left 1 _) hU P.hFast
  rw [Nat.add_sub_cancel] at hC'
  have hst := state_saved_of_update S Sched x (r * S.C.R) v A' P.hDiv P.hMono
    (P.member1 le_rfl hvH hEnd) hU
  exact ⟨v, hvH, A', C', L, hU, hC', hst.trans hC', ancestorEq_refl L, hLC',
    Or.inl ⟨rfl, P.hFast, P.hL⟩⟩

/-- A block on a member's confirmation of a slot `σ ≥ r * R + k` is a line source of slot `σ`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem source_conf (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ : ℕ} {u : V}
    {C X : Block V} (hσ : r * S.C.R + S.C.k ≤ σ) (hu : u ∈ Hon S Sched σ)
    (hEnd : supportCutoff S (σ + 1) ≤ tAwakeEnd)
    (hC : (stateBefore x (supportCutoff S (σ + 1) + 1) u).A.saved_confirmation σ = some C)
    (hXC : X.AncestorEq C) : LineSource S Sched x r H₂ σ X := by
  obtain ⟨A₀, hU, hS⟩ := update_of_saved_confirmation S Sched x σ u C P.hDiv P.hMono
    (P.member1 (by omega) hu hEnd) hC
  exact ⟨u, hu, A₀, C, C, hU, hS, hC, hXC, ancestorEq_refl C, Or.inr (Or.inr hσ)⟩

/-- A lock entry `u` holds before `t`, honest then, is of a slot `μ` whose update ran before `t`,
on `u`'s confirmation of slot `μ`; and its block is a line source of slot `μ` when
`μ ≥ r * R + 1`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem source_lock (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {t : ℕ} {u : V}
    {e : LockEntry V} (hu : u ∉ Sched.adv (t : Int)) (hEnd : t ≤ tAwakeEnd)
    (he : e ∈ (stateBefore x t u).A.lock_entries) :
    ∃ μ : ℕ, e.d = S.C.t_ (μ + S.C.k) + 5 * S.C.Δ ∧ supportCutoff S (μ + 1) < t ∧
      (∃ C' : Block V,
        (stateBefore x (supportCutoff S (μ + 1) + 1) u).A.saved_confirmation μ = some C' ∧
        e.B.AncestorEq C') ∧
      (r * S.C.R + 1 ≤ μ → LineSource S Sched x r H₂ μ e.B) := by
  obtain ⟨μ, hd, hcut, -, A₀, hA₀, e₀, he₀, -, -, -, ⟨C₀, hC₀, he₀C₀⟩, hkind, htr⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem39_lock_entry_provenance S Sched x t u e P.hDiv he
  obtain ⟨e₁, -, -, hB₁, hB₁₀⟩ := htr t hcut le_rfl
  have heB₀ : e.B.AncestorEq e₀.B := ancestorEq_trans hB₁ hB₁₀
  have huH : u ∈ Hon S Sched μ := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _,
      fun h => hu (P.hMono _ _ (by exact_mod_cast hcut.le) h)⟩
  have hst := state_saved_of_update S Sched x μ u A₀ P.hDiv P.hMono
  refine ⟨μ, hd, hcut, ?_, fun hμ => ?_⟩
  · obtain ⟨μ', hd', hcut', C', hsv, heC'⟩ := lock_entry_confirmation S Sched x t u e P.hDiv he
    have hμμ : μ' = μ := by
      have h1 : S.C.t_ (μ' + S.C.k) = S.C.t_ (μ + S.C.k) := add_right_cancel (hd'.symm.trans hd)
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := t_lt_of_lt S (show μ' + S.C.k < μ + S.C.k by omega)
        rw [h1] at this
        exact lt_irrefl _ this
      · have := t_lt_of_lt S (show μ + S.C.k < μ' + S.C.k by omega)
        rw [h1] at this
        exact lt_irrefl _ this
    subst hμμ
    exact ⟨C', hsv, heC'⟩
  · have hst' := hst (P.member1 (by omega) huH (by omega)) hA₀
    exact ⟨u, huH, A₀, C₀, e₀.B, hA₀, hC₀, hst'.trans hC₀, heB₀, he₀C₀,
      Or.inr (Or.inl ⟨hμ, hkind⟩)⟩

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- Two line sources of slots `μ ≤ μ' ≤ σ` are compatible, when the invariant holds at every slot
up to `σ`: of one slot, by Lemma 32; of two slots, the later source's confirmation extends the
earlier source.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem sources_compatible_le (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ')
    (hEnd : supportCutoff S (σ + 1) ≤ tAwakeEnd) {μ μ' : ℕ} {X X' : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hX' : LineSource S Sched x r H₂ μ' X')
    (hμμ : μ ≤ μ') (hμ' : μ' ≤ σ) : X.compatible X' = true := by
  have hs := hX.slot_ge
  have hs' := hX'.slot_ge
  obtain ⟨u', hu', A₀', C₀', X₀', -, -, hC₀', hXX₀', hX₀C₀', -⟩ := hX'
  have hX'C : X'.AncestorEq C₀' := ancestorEq_trans hXX₀' hX₀C₀'
  have hEnd' : supportCutoff S (μ' + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd
  rcases Nat.lt_or_eq_of_le hμμ with hlt | heq
  · have hXC := (hG μ' hμ' μ X hX (by omega)).2.2 u' hu' C₀' hC₀'
    exact compatible_of_ancestorEq_both hXC hX'C ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))
  · subst heq
    obtain ⟨u, hu, A₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := hX
    have hcΔ : supportCutoff S μ + Δ S ≤ tAwakeEnd := by
      have := supportCutoff_eq S μ
      have := supportCutoff_eq S (μ + 1)
      have := voteTime_succ S μ
      omega
    exact compatible_of_ancestorEq_both (ancestorEq_trans hXX₀ hX₀C₀) hX'C
      (lem32_saved_confirmations_compatible_state_upTo S Sched x GST μ u u' C₀ C₀' P.hDiv P.hMono
        (P.hSync.mono hcΔ) (P.hCatch.mono hcΔ) (P.hRoots.mono hEnd') (P.gst hs).2.2
        (P.member1 hs hu hEnd')
        (P.member1 hs hu' hEnd') hC₀ hC₀')

/-- Two line sources of slots at most `σ` are compatible, when the invariant holds at every slot
up to `σ`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem sources_compatible (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ')
    (hEnd : supportCutoff S (σ + 1) ≤ tAwakeEnd) {μ μ' : ℕ} {X X' : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hX' : LineSource S Sched x r H₂ μ' X')
    (hμ : μ ≤ σ) (hμ' : μ' ≤ σ) : X.compatible X' = true := by
  rcases le_total μ μ' with h | h
  · exact P.sources_compatible_le hG hEnd hX hX' h hμ'
  · exact compatible_symm' (P.sources_compatible_le hG hEnd hX' hX h hμ)

end PartAHypsUpTo

open GoldilocksCorrectness.Statements.Routines (lem15_tick_updates_confirmation lem49_tick_attests)
open GoldilocksCorrectness.Proofs.Routines (ac_to_fg_source_mem ac_to_fg_source_fast
  tick_attest_awake awakeSince_of_record_awake create_attestation_cases)

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **A certificate at a height greater than `H₂` names an entry of a line source.** A progress certificate at a
height `h > H₂` on the chain of a block `w` holds after `j` steps, within the phase, names the root
of an entry block `E` at the height `h` that is a line source of a slot `μ` whose update ran by
then: `E` is the entry of the fast block an honest attester's update made fast at the action time
of a round `r' ≥ r` (A1), of kind (a) when `r' = r` (its height is then `H₂ + 1`, A2).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem cert_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x[j].time ≤ tAwakeEnd)
    (hY : Y ∈ (x[j][w].st).S.T) (hJ : ProgressCertOn Y h T) (hH : H₂ < h) :
    ∃ (μ : ℕ) (E : Block V), supportCutoff S (μ + 1) ≤ x[j].time ∧
      LineSource S Sched x r H₂ μ E ∧ IsEntry S.C E ∧ (chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  have hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int) :=
    fewerThanQuorum_of_fewerThanThird Sched _
      (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hj) P.hThird)
  obtain ⟨A, hqA, hA⟩ := hJ
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := lem74_honest_attestations_recorded S Sched x P.hU j w Y a hY hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have htj : t' ≤ x[j].time := by
    rw [← (time_of_lbl_tickAllAwake x hl).2]
    exact time_mono x hj'
  have hge : aR S r ≤ t' := by
    by_contra hlt
    have hle := P.hOld j' t' u a' hl (Nat.lt_of_not_le hlt) hAw hHon hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  obtain ⟨r', rfl⟩ := attest_time_round S Sched x hl hsent
  have hrr : r ≤ r' := by
    by_contra hlt
    have : r' * S.C.R + 1 < r * S.C.R + 1 := by
      have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt)
        (show 0 < S.C.R by have := S.C.R_ge_two; omega)
      omega
    have := supportCutoff_lt S this
    exact absurd hge (Nat.not_le.mpr this)
  obtain ⟨A₀, X, hU, hXf, hXT, hXh, hXT'⟩ :=
    fast_source_of_attestation S Sched x r' u a' ⟨j', hl, hAw, hHon, hsent⟩
  obtain ⟨hE1, hE2, hE3⟩ := GoldilocksCorrectness.Proofs.Routines.isEntry_T_h S.C X
  have hEnd' : supportCutoff S (r' * S.C.R + 1) ≤ tAwakeEnd := le_trans htj hj
  have huH : u ∈ Hon S Sched (r' * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hHon⟩
  have hU' : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).A
        ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).S)
      ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int) (r' * S.C.R + 1) = .ok A₀ := hU
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved S.C S.P _ A₀ _ _
      (r' * S.C.R + 1) X (Nat.le_add_left 1 _) hU' hXf
  rw [Nat.add_sub_cancel] at hC₀
  have hrR : r * S.C.R ≤ r' * S.C.R := Nat.mul_le_mul_right _ hrr
  have hst := state_saved_of_update S Sched x (r' * S.C.R) u A₀ P.hDiv P.hMono
    (P.member1 hrR huH hEnd') hU'
  have hkind : (r' * S.C.R = r * S.C.R ∧ X ∈ A₀.fast_blocks ∧ (chainStateOf S.C X).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ r' * S.C.R ∧ (X ∈ A₀.fast_blocks ∨
        slow_test S.C (expireLocks (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).A
          ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int))
          (fg_to_ac (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).S) (r' * S.C.R) X =
            true)) ∨
      r * S.C.R + S.C.k ≤ r' * S.C.R := by
    rcases Nat.lt_or_eq_of_le hrr with hlt | heq
    · refine Or.inr (Or.inl ⟨?_, Or.inl hXf⟩)
      have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
      have h2 := S.C.R_ge_two
      rw [Nat.succ_mul] at h1
      omega
    · subst heq
      refine Or.inl ⟨rfl, hXf, ?_⟩
      have hle := held_height_le_before_action S Sched x tAwakeEnd r H₂ (aR S r) u X P.hU
        P.hThird P.hOld le_rfl hEnd' hXT
      rw [hXh, hh'] at hle ⊢
      exact Nat.le_antisymm hle (Nat.succ_le_of_lt hH)
  refine ⟨r' * S.C.R, (chainStateOf S.C X).T_h, htj, ⟨u, huH, A₀, C₀, X, hU', hC₀,
    hst.trans hC₀, hE3, hXC₀, hkind⟩, hE1, by rw [hE2, hXh, hh'], ?_⟩
  rw [← hT', ← hXT']

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- A line source of slot `μ` is a block of an honest validator's tree at a step at a time at most
the support cutoff of slot `μ + 1`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem source_inHonestTreeBy (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {μ : ℕ}
    {X : Block V} (hX : LineSource S Sched x r H₂ μ X) :
    inHonestTreeBy x (supportCutoff S (μ + 1)) X := by
  obtain ⟨u, hu, A₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := hX
  have hu' : u ∉ Sched.adv ((supportCutoff S (μ + 1) : ℕ) : Int) := by
    unfold Hon roundMembers at hu
    exact (Finset.mem_sdiff.1 hu).2
  refine ⟨stepBefore x (supportCutoff S (μ + 1) + 1), u, ?_, time_stepBefore_succ_le x _, ?_⟩
  · intro hadv
    exact hu' (P.hMono _ _ (Int.ofNat_le.2 (time_stepBefore_succ_le x _)) hadv)
  · exact ancestors_mem_T_of_exec S Sched x _ u C₀ X
      (saved_confirmation_mem_T_of_exec S Sched x _ u μ C₀ hC₀) (ancestorEq_trans hXX₀ hX₀C₀)

/-- A line source of slot `μ` reaches every validator honest at the view freeze of slot `μ` whose
finalized block then is compatible with it, by that view freeze.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem source_held (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {μ : ℕ}
    {X : Block V} {w : V} (hX : LineSource S Sched x r H₂ μ X)
    (hEnd : supportCutoff S (μ + 1) ≤ tAwakeEnd)
    (hw : w ∉ Sched.adv ((viewFreeze S μ : ℕ) : Int))
    (hF : (stateBefore x (viewFreeze S μ) w).S.F.compatible X = true) :
    X ∈ (stateBefore x (viewFreeze S μ) w).S.T := by
  have hs := hX.slot_ge
  obtain ⟨u, hu, A₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := hX
  have hCT := saved_confirmation_mem_T_supportCutoff S Sched x μ u C₀ P.hDiv P.hMono
    (P.member1 hs hu hEnd) hC₀
  have hXT := ancestors_mem_T_of_exec S Sched x _ u C₀ X hCT (ancestorEq_trans hXX₀ hX₀C₀)
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := times_eq S μ
  obtain ⟨-, hc1', -, -, -⟩ := times_eq S (μ + 1)
  have hvf : viewFreeze S μ = supportCutoff S μ + Δ S := by omega
  have hc1 : supportCutoff S μ ≤ supportCutoff S (μ + 1) := by omega
  have hvc : viewFreeze S μ ≤ supportCutoff S (μ + 1) := by omega
  have hdw := P.dws hs
  have hdw' := dutyWindowStart_le_voteTime S μ
  rw [hvf] at hw hF ⊢
  refine mem_T_before_add_delay_of_held_upTo P.hDiv P.hMono (P.hSync.mono (by omega))
    (P.hCatch.mono (by omega))
    (P.hRoots.mono (by omega))
    P.hParent (t₁ := supportCutoff S μ) (t := supportCutoff S μ) (by omega)
    le_rfl (P.gst hs).2.2 ?_ hXT ?_ hF
  · exact (P.member hu hEnd _ (by omega) hc1).2
  · exact fun t' h1 h2 => P.window hw (by omega) t' (by omega) h2

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- `v` holds `L` before the support cutoff of slot `r * R`, and so before `a_r`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem L_held_v (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    (hEnd : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd) :
    L ∈ (stateBefore x (supportCutoff S (r * S.C.R)) v).S.T ∧
      L ∈ (stateBefore x (aR S r) v).S.T := by
  have hvH : v ∈ Hon S Sched (r * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, P.hv⟩
  have hU : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (r * S.C.R + 1)) v).A
        ((supportCutoff S (r * S.C.R + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (r * S.C.R + 1)) v).S)
      ((supportCutoff S (r * S.C.R + 1) : ℕ) : Int) (r * S.C.R + 1) = .ok A' := P.hUpdate
  obtain ⟨C', hC', hLC'⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved S.C S.P _ A' _ _
      (r * S.C.R + 1) L (Nat.le_add_left 1 _) hU P.hFast
  rw [Nat.add_sub_cancel] at hC'
  have hst := state_saved_of_update S Sched x (r * S.C.R) v A' P.hDiv P.hMono
    (P.member1 le_rfl hvH hEnd) hU
  have hCT := saved_confirmation_mem_T_supportCutoff S Sched x (r * S.C.R) v C' P.hDiv P.hMono
    (P.member1 le_rfl hvH hEnd) (hst.trans hC')
  have h1 := ancestors_mem_T_of_exec S Sched x _ v C' L hCT hLC'
  refine ⟨h1, (stateBefore_grows x P.hDiv v (supportCutoff_mono S (Nat.le_succ _))).1 h1⟩

/-- Every validator honest at the view freeze of slot `r * R` holds `L` then.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem L_held (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    (hEnd : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd) {w : V}
    (hw : w ∉ Sched.adv ((viewFreeze S (r * S.C.R) : ℕ) : Int)) :
    L ∈ (stateBefore x (viewFreeze S (r * S.C.R)) w).S.T := by
  have hvf : viewFreeze S (r * S.C.R) ≤ aR S r := by
    obtain ⟨-, -, hf0, hs0, -⟩ := times_eq S (r * S.C.R)
    obtain ⟨-, hc1, -, -, -⟩ := times_eq S (r * S.C.R + 1)
    show viewFreeze S (r * S.C.R) ≤ supportCutoff S (r * S.C.R + 1)
    omega
  refine P.source_held (P.source_L hEnd) hEnd hw ((compatible_iff _ _).2 (Or.inl ?_))
  exact finalized_ancestor_of_fast_block S Sched x tAwakeEnd r H₂ _ v w L P.hMono P.hU
    (P.hRoots.mono hEnd)
    P.hThird P.hOld hEnd P.hv (P.L_held_v hEnd).2 P.hL hvf hw

/-- **The finalized block is compatible with every line source.** At a time `t ≥ 1` up to the
support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ`,
an honest validator's finalized block is compatible with every line source of a slot at most `σ`:
at a finalization height at most `H₂` it is an ancestor of `L` (Lemma 89a), at a greater height it is a
line source itself (`cert_source`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem F_compat (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht1 : 1 ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) :
    (stateBefore x t w).S.F.compatible X = true := by
  have hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ _)) hEnd
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  obtain ⟨D, hD, hFD⟩ :=
    GoldilocksCorrectness.Statements.Executions.finalizedFromChain_of_exec S Sched x
      (stepBefore x t) w
  show (x[stepBefore x t][w].st).S.F.compatible X = true
  rw [hFD]
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  by_cases hle : (chainStateOf S.C D).h_F ≤ H₂
  · have htv : x[stepBefore x (aR S r)].time ≤ aR S r := time_stepBefore_le x _
    have hv' : v ∉ Sched.adv (x[stepBefore x (aR S r)].time : Int) :=
      fun h => P.hv (P.hMono _ _ (by exact_mod_cast htv) h)
    have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
        (max (x[stepBefore x t].time : Int) (x[stepBefore x (aR S r)].time : Int)) :=
      adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast hjE)
        (by exact_mod_cast (show x[stepBefore x (aR S r)].time ≤ tAwakeEnd by
          have : aR S r ≤ tAwakeEnd := hEndR
          omega))) P.hThird
    have hFL := lem68_honest_past_finalized S Sched x P.hU P.hRoots (stepBefore x t)
      (stepBefore x (aR S r)) w v D L hT hw' hv' hD (P.L_held_v hEndR).2
      (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE (le_trans htv hEndR))
    exact compatible_of_ancestorEq_compatible hFL
      (P.sources_compatible hG hEnd1 (P.source_L hEndR) hX hσ hμ)
  · have hlt : H₂ < (chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (chainStateOf S.C D).F ∈ (x[stepBefore x t][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w D _ hD hFanc
    obtain ⟨μ', E, hcut, hE, -, -, hEr⟩ := P.cert_source hjE hD
      (progressCertOn_of_justificationCertOn hJC) hlt
    have hμ' : μ' ≤ σ := by
      by_contra h
      have := supportCutoff_mono S (show σ + 2 ≤ μ' + 1 by omega)
      omega
    have hFE : (chainStateOf S.C D).F = E :=
      P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hFT⟩
        (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
    rw [hFE]
    exact P.sources_compatible hG hEnd1 hE hX hμ' hμ

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- From the view freeze of slot `r * R` on, an honest validator holds `L`, with its own chain
state, at a height at most its `h_max`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem L_tall (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    (hEnd : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd) {t : ℕ} {w : V}
    (ht0 : viewFreeze S (r * S.C.R) ≤ t) (hw : w ∉ Sched.adv (t : Int)) :
    L ∈ (stateBefore x t w).S.T ∧ (stateBefore x t w).S.σ L = chainStateOf S.C L ∧
      H₂ + 1 ≤ (stateBefore x t w).S.h_max := by
  have hw0 : w ∉ Sched.adv ((viewFreeze S (r * S.C.R) : ℕ) : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast ht0) h)
  have hLT := (stateBefore_grows x P.hDiv w ht0).1 (P.L_held hEnd hw0)
  have hInv := (lem11_node_invariant S Sched x (stepBefore x t) w).1
  have hσ : (stateBefore x t w).S.σ L = chainStateOf S.C L := hInv.2.2.2.2.2.1 L hLT
  have hge : ((stateBefore x t w).S.σ L).h ≤ (stateBefore x t w).S.h_max :=
    hInv.2.2.2.2.2.2.2.2.2.1.2.1.2 L hLT
  rw [hσ, P.hL] at hge
  exact ⟨hLT, hσ, hge⟩

/-- **The root is compatible with every line source.** From the view freeze of slot `r * R` to
the support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to
`σ`, an honest validator's fork-choice root is compatible with every line source of a slot at
most `σ`: the finalized block (`F_compat`); or the justified block, a line source when its height
is greater than `H₂` (`cert_source`), and `L` or an ancestor of `L` otherwise (the contest rule).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem root_compat (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht0 : viewFreeze S (r * S.C.R) ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) :
    (get_fc_root (stateBefore x t w).S).compatible X = true := by
  have hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ _)) hEnd
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  have ht1 : 1 ≤ t := by
    obtain ⟨-, -, hf0, -, hΔ⟩ := times_eq S (r * S.C.R)
    omega
  obtain ⟨hLT, hσL, hM⟩ := P.L_tall hEndR ht0 hw
  by_cases hR : get_fc_root (stateBefore x t w).S = (stateBefore x t w).S.F
  · rw [hR]
    exact P.F_compat hG hσ hEnd ht1 ht hw hX hμ
  have key : (stateBefore x t w).S.h_max = (stateBefore x t w).S.h_j + 1 ∧
      get_fc_root (stateBefore x t w).S = (stateBefore x t w).S.J := by
    rcases root_cases (stateBefore x t w).S with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  rw [key.2]
  by_cases hlt : H₂ < (stateBefore x t w).S.h_j
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x[stepBefore x t][w].st).S.T := hD
    have hJT : (chainStateOf S.C D).J ∈ (x[stepBefore x t][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w D _ hD' hJanc
    obtain ⟨μ', E, hcut, hE, -, -, hEr⟩ := P.cert_source hjE hD'
      (progressCertOn_of_justificationCertOn hJC) hlt
    have hμ' : μ' ≤ σ := by
      by_contra h
      have := supportCutoff_mono S (show σ + 2 ≤ μ' + 1 by omega)
      omega
    have hJE : (chainStateOf S.C D).J = E :=
      P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hJT⟩
        (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
    rw [hJD, hJE]
    exact P.sources_compatible hG hEnd1 hE hX hμ' hμ
  · have hhj : (stateBefore x t w).S.h_j = H₂ := by
      have := key.1
      have h1 : (stateBefore x t w).S.h_j ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    have hLX := P.sources_compatible hG hEnd1 (P.source_L hEndR) hX hσ hμ
    by_cases h0 : (chainStateOf S.C D).h_j = 0
    · have hg := (chainStateOf_J_spec S.C D).2.1 h0
      rw [hJD, hg]
      exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))
    · have hJh := (chainStateOf_J_spec S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (stateBefore x t w).S.F.AncestorEq (stateBefore x t w).S.J := by
        have := F_ancestorEq_fc_root_of_stateBefore S Sched x t w
        rw [key.2] at this
        exact this
      have hFL : (stateBefore x t w).S.F.AncestorEq L := by
        rcases (compatible_iff _ _).1 (P.F_compat hG hσ hEnd ht1 ht hw (P.source_L hEndR) hσ)
          with h | h
        · exact h
        · exfalso
          have h1 := chainStateOf_height_mono S.C (ancestorEq_trans h hFJ)
          rw [hJD, hJh, ← hhjD, hhj, P.hL] at h1
          exact Nat.lt_irrefl _ (Nat.lt_of_succ_le h1)
      have hRL := fc_root_ancestorEq_of_tall _ L hLT hFL (by
        rw [hσL, P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact compatible_of_ancestorEq_compatible hRL hLX

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- A block whose chain state has a height `h ≥ H₂ + 2`, held by an honest validator in the phase,
has an ancestor entry at the height `h − 1` that is a line source of a slot whose update ran
before then.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem tall_entry (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {t : ℕ} {w : V}
    (ht1 : 1 ≤ t) (htE : t ≤ tAwakeEnd) (hw : w ∉ Sched.adv (t : Int)) {Y : Block V}
    (hY : Y ∈ (stateBefore x t w).S.T) (hYh : H₂ + 2 ≤ (chainStateOf S.C Y).h) :
    ∃ (μ' : ℕ) (E : Block V), supportCutoff S (μ' + 1) < t ∧
      LineSource S Sched x r H₂ μ' E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = (chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  have hY' : Y ∈ (x[stepBefore x t][w].st).S.T := hY
  obtain ⟨Y', hY'Y, -, -, -, hT', hcert⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem67_first_advance S.C Y
      ((chainStateOf S.C Y).h - 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  have hY'T := ancestors_mem_T_of_exec S Sched x _ w Y Y' hY' hY'Y
  have hT'T := ancestors_mem_T_of_exec S Sched x _ w Y' _ hY'T hT'
  obtain ⟨μ', E, hcut, hE, hEe, hEh, hEr⟩ := P.cert_source hjE hY'T hcert
    (by unfold Height at *; omega)
  have hTE := P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hT'T⟩
    (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
  refine ⟨μ', E, lt_of_le_of_lt hcut htj, hE, hEe, hEh, ?_⟩
  rw [← hTE]
  exact ancestorEq_trans hT' hY'Y

/-- **A viable block on a line source's chain.** From the vote time of slot `σ + 1` to the
support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ` and
an honest validator's root is a line source `X` of a slot at most `σ` or an ancestor of it: some
block `W`, `X` or a descendant of `X`, held by the validator before the view freeze of slot `σ`,
has a chain-state height at least its `head_height_floor`. `W` is `L` or `X` when `h_max` is
`H₂ + 1`; otherwise the state is not contested (the entries at `h_max − 1` are one block, a line
source, Lemma 67 and `cert_source`) and `W` is that entry or `X`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem viable_candidate (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht0 : voteTime S (σ + 1) ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (get_fc_root (stateBefore x t w).S).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (stateBefore x (viewFreeze S σ) w).S.T ∧
      head_height_floor (stateBefore x t w).S ≤ (chainStateOf S.C W).h := by
  have hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ _)) hEnd
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := times_eq S σ
  obtain ⟨hvσ1, -, -, -, -⟩ := times_eq S (σ + 1)
  have hfv : viewFreeze S σ ≤ t := by omega
  have hfR : viewFreeze S (r * S.C.R) ≤ viewFreeze S σ := by
    have := slotStart_mono S hσ
    have := viewFreeze_eq S (r * S.C.R)
    omega
  have hEndE : t ≤ tAwakeEnd := le_trans ht hEnd
  have hwf : ∀ t' : ℕ, t' ≤ t → w ∉ Sched.adv (t' : Int) :=
    fun t' h h' => hw (P.hMono _ _ (by exact_mod_cast h) h')
  -- `w`'s finalized blocks up to `t` are ancestors of `X`
  have hFX : ∀ t' : ℕ, t' ≤ t → (stateBefore x t' w).S.F.AncestorEq X := fun t' h =>
    ancestorEq_trans (stateBefore_grows x P.hDiv w h).2.1
      (ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x t w) hRX)
  -- a line source of a slot at most `σ` on `X`'s chain is held before the view freeze of `σ`
  have hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource S Sched x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ (stateBefore x (viewFreeze S σ) w).S.T := by
    intro μ₁ X₁ hX₁ hμ₁ hXX₁
    have hf1 : viewFreeze S μ₁ ≤ viewFreeze S σ := by
      have := slotStart_mono S hμ₁
      have := viewFreeze_eq S μ₁
      omega
    have := P.source_held hX₁ (le_trans (supportCutoff_mono S (by omega)) hEnd1)
      (hwf _ (by omega)) ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans
        (hFX _ (by omega)) hXX₁)))
    exact (stateBefore_grows x P.hDiv w hf1).1 this
  obtain ⟨hLT, hσL, hM⟩ := P.L_tall hEndR (le_trans hfR hfv) hw
  have hXh := hheld hX hμ (ancestorEq_refl X)
  by_cases hMle : (stateBefore x t w).S.h_max ≤ H₂ + 1
  · have hfl := floor_le_h_max (stateBefore x t w).S
    rcases (compatible_iff _ _).1 (P.sources_compatible hG hEnd1 (P.source_L hEndR) hX hσ hμ)
      with h | h
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := chainStateOf_height_mono S.C h
      rw [P.hL] at this
      unfold Height at *
      omega
    · refine ⟨L, h, (stateBefore_grows x P.hDiv w hfR).1
        (P.L_held hEndR (hwf _ (le_trans hfR hfv))), ?_⟩
      rw [P.hL]
      unfold Height at *
      omega
  · have hM2 : H₂ + 2 ≤ (stateBefore x t w).S.h_max := by unfold Height at *; omega
    have ht1 : 1 ≤ t := by omega
    obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
    obtain ⟨μ', E, hcut, hE, hEe, hEh, hEY⟩ := P.tall_entry ht1 hEndE hw hY (by rw [hYh]; exact hM2)
    have hμ' : μ' ≤ σ := by
      by_contra h
      have := supportCutoff_mono S (show σ + 2 ≤ μ' + 1 by omega)
      omega
    rw [hYh] at hEh
    -- the state is not contested
    have hnc : fg_contest (stateBefore x t w).S = false := by
      cases hcs : fg_contest (stateBefore x t w).S
      · rfl
      exfalso
      obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ := fg_contest_spec _ hcs
      have hσB : (stateBefore x t w).S.σ B = chainStateOf S.C B :=
        (lem11_node_invariant S Sched x (stepBefore x t) w).1.2.2.2.2.2.1 B hBT
      have hBh' : ((stateBefore x t w).S.σ B).h = (stateBefore x t w).S.h_max := hBh
      rw [hσB] at hBh'
      clear hBh
      have hBh := hBh'
      obtain ⟨μB, EB, hcutB, hEB, hEBe, hEBh, hEBB⟩ := P.tall_entry ht1 hEndE hw hBT
        (by rw [hBh]; exact hM2)
      have hμB : μB ≤ σ := by
        by_contra h
        have := supportCutoff_mono S (show σ + 2 ≤ μB + 1 by omega)
        omega
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
      have htj : x[stepBefore x t].time < t := by
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have := time_stepBefore_succ_le x t'
        omega
      have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) := hwf _ htj.le
      have hlt : H₂ < (chainStateOf S.C D).h_j := by
        rw [← hhjD]
        unfold Height at *
        omega
      obtain ⟨hJC, hJanc, hJh⟩ := (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified
        S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hD' : D ∈ (x[stepBefore x t][w].st).S.T := hD
      have hJT : (chainStateOf S.C D).J ∈ (x[stepBefore x t][w].st).S.T :=
        ancestors_mem_T_of_exec S Sched x _ w D _ hD' hJanc
      obtain ⟨μJ, EJ, hcutJ, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source (by omega) hD'
        (progressCertOn_of_justificationCertOn hJC) hlt
      have hμJ : μJ ≤ σ := by
        by_contra h
        have := supportCutoff_mono S (show σ + 2 ≤ μJ + 1 by omega)
        omega
      have hJE : (chainStateOf S.C D).J = EJ :=
        P.hRoots _ _ ⟨stepBefore x t, w, hw', by omega, hJT⟩
          (inHonestTreeBy_mono x (le_trans hcutJ (by omega)) (P.source_inHonestTreeBy hEJ)) hEJr
      have hEE : EJ = EB := entry_eq_of_compatible S.C hEJe hEBe (by
          rw [hEJh, hEBh, ← hhjD, hBh, hbox]
          unfold Height at *
          omega)
        (P.sources_compatible hG hEnd1 hEJ hEB hμJ hμB)
      apply hJB
      rw [hJD, hJE, hEE]
      exact hEBB
    have hfloor : head_height_floor (stateBefore x t w).S = (stateBefore x t w).S.h_max - 1 :=
      head_height_floor_of_not_contested _ hnc
    rcases (compatible_iff _ _).1 (P.sources_compatible hG hEnd1 hX hE hμ hμ') with h | h
    · exact ⟨E, h, hheld hE hμ' h, by rw [hfloor, hEh]⟩
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := chainStateOf_height_mono S.C h
      rw [hfloor, ← hEh]
      exact this

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **The frame at a time relative to a line source.** From the vote time of slot `σ + 1` to the
support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ`: an
honest validator's root is compatible with every line source `X` of a slot at most `σ`; when the
root is `X` or an ancestor of `X`, some viable head of its frame is `X` or a descendant of `X`;
and its finalized block is compatible with `X`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem frame_source_at (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht0 : voteTime S (σ + 1) ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) :
    (fg_to_ac (stateBefore x t w).S).fc_root.compatible X = true ∧
    ((fg_to_ac (stateBefore x t w).S).fc_root.AncestorEq X →
      ∃ W ∈ (fg_to_ac (stateBefore x t w).S).tree,
        W ∈ (fg_to_ac (stateBefore x t w).S).viable_heads ∧ X.AncestorEq W) ∧
    (stateBefore x t w).S.F.compatible X = true := by
  obtain ⟨-, -, hfσ, hsσ, hΔ⟩ := times_eq S σ
  obtain ⟨hvσ1, -, -, -, -⟩ := times_eq S (σ + 1)
  have hfR : viewFreeze S (r * S.C.R) ≤ t := by
    have := slotStart_mono S hσ
    have := viewFreeze_eq S (r * S.C.R)
    omega
  refine ⟨by rw [fc_root_eq]; exact P.root_compat hG hσ hEnd hfR ht hw hX hμ, fun hR => ?_,
    P.F_compat hG hσ hEnd (by omega) ht hw hX hμ⟩
  have hR' : (get_fc_root (stateBefore x t w).S).AncestorEq X := by
    rw [← fc_root_eq]; exact hR
  obtain ⟨W, hXW, hWT, hφ⟩ := P.viable_candidate hG hσ hEnd ht0 ht hw hX hμ hR'
  have hWT' := (stateBefore_grows x P.hDiv w (show viewFreeze S σ ≤ t by omega)).1 hWT
  have hFW : (stateBefore x t w).S.F.AncestorEq W :=
    ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x t w) (ancestorEq_trans hR' hXW)
  have hσW : (stateBefore x t w).S.σ W = chainStateOf S.C W :=
    (lem11_node_invariant S Sched x (stepBefore x t) w).1.2.2.2.2.2.1 W hWT'
  refine ⟨W, (mem_fg_to_ac_tree _ _).2 ⟨hWT', hFW⟩, ?_, hXW⟩
  refine ((GoldilocksCorrectness.Statements.Routines.lem56_frame_of_shape _ _ _
    (show FrameShape (stateBefore x t w).S (get_fc_root (stateBefore x t w).S)
      (head_height_floor (stateBefore x t w).S) from ⟨rfl, rfl⟩)).2.2 W).2
    ⟨hWT', hFW, ancestorEq_trans hR' hXW, ?_⟩
  rw [hσW]
  exact hφ

/-- **The step's frame conditions relative to a line source.** In the phase, when the invariant
holds at every slot up to `σ`, every validator honest at the support cutoff of slot `σ + 2`
satisfies `StepFrameAt` relative to every line source of a slot at most `σ`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem stepFrame_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd)
    (hw : w ∉ Sched.adv ((supportCutoff S (σ + 2) : ℕ) : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) : StepFrameAt S Sched x X σ w := by
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := times_eq S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := times_eq S (σ + 1)
  obtain ⟨-, hcσ2, -, -, -⟩ := times_eq S (σ + 2)
  have hv1c : voteTime S (σ + 1) ≤ supportCutoff S (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢
    omega
  have hwv : w ∉ Sched.adv ((voteTime S (σ + 1) : ℕ) : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast hv1c) h)
  obtain ⟨h1, -, -⟩ := P.frame_source_at hG hσ hEnd le_rfl hv1c hwv hX hμ
  obtain ⟨-, -, h3⟩ := P.frame_source_at hG hσ hEnd hv1c le_rfl hw hX hμ
  refine ⟨h1, fun hR tree htree => ?_, h3⟩
  have hR' : (get_fc_root (stateBefore x (voteTime S (σ + 1)) w).S).AncestorEq X := by
    rw [← fc_root_eq]; exact hR
  obtain ⟨W, hXW, hWT, hφ⟩ := P.viable_candidate hG hσ hEnd le_rfl hv1c hwv hX hμ hR'
  obtain ⟨hWt, hWv⟩ := proposal_viable_head_at S Sched x (viewFreeze S σ) (σ + 1) w W _ _ tree
    P.hDiv hWT (by rw [Nat.add_sub_cancel]) (by omega) ⟨rfl, rfl⟩
    (ancestorEq_trans hR' hXW) hφ htree
  exact ⟨W, hWt, hWv, hXW⟩

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **An old lock and a slow block.** A lock entry `e₁` a validator `w` holds live at the vote
time of slot `μ + 1`, of a slot `μ₀ < μ`, is compatible with a block `X₀` passing the slow test in
the update of slot `μ` of a member `u`: the slow test reads `u`'s confirmation of slot `μ₀`
(Lemma 37), which extends `X₀` and is compatible with `w`'s confirmation of slot `μ₀`, which
extends `e₁`'s block (Lemmas 39, 40, 31).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem old_lock_compat (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {μ μ₀ : ℕ}
    (hμ : r * S.C.R + 1 ≤ μ) (hEnd1 : supportCutoff S (μ + 1) ≤ tAwakeEnd) {u : V} (hu : u ∈ Hon S Sched μ)
    {X₀ : Block V}
    (hslow : slow_test S.C (expireLocks (stateBefore x (supportCutoff S (μ + 1)) u).A
      ((supportCutoff S (μ + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (μ + 1)) u).S) μ X₀ = true)
    {w : V} (hwin : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (μ + 2) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    {e₁ : LockEntry V} (he₁' : e₁ ∈ (stateBefore x (voteTime S (μ + 1)) w).A.lock_entries)
    (hlive : ((voteTime S (μ + 1) : ℕ) : Int) < e₁.d)
    (hd₀ : e₁.d = S.C.t_ (μ₀ + S.C.k) + 5 * S.C.Δ) (hμ₀hi : μ₀ + 1 ≤ μ) :
    e₁.B.compatible X₀ = true := by
  have hk := S.C.k_ge_two
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := times_eq S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := times_eq S (μ + 1)
  have hcm := supportCutoff_mono S hμ₀hi
  obtain ⟨hk1, hsl⟩ := GoldilocksCorrectness.Statements.Routines.lem37_slow_test_saved_confirmations
    S.C _ _ μ X₀ hslow
  have hμ₀lo : μ + 1 - S.C.k ≤ μ₀ :=
    GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
      (μ + 1 - S.C.k) μ₀ (voteTime S (μ + 1)) e₁ hd₀ hlive
      (by rw [show μ + 1 - S.C.k + S.C.k = μ + 1 by omega])
  obtain ⟨Cu, hCu, -, hX₀Cu⟩ := hsl μ₀ hμ₀lo (show μ₀ < μ by omega)
  have hCu' : (stateBefore x (supportCutoff S (μ + 1)) u).A.saved_confirmation μ₀ = some Cu := hCu
  obtain ⟨-, -, ⟨Au, hAu, hSu⟩, -⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem40_saved_confirmation_provenance S Sched x
      (supportCutoff S (μ + 1)) u μ₀ Cu P.hDiv hCu'
  obtain ⟨μ₁, hd₁, -, -, Aw, hAw, e₂, -, hd₂, -, -, ⟨Cw, hCw, he₂Cw⟩, -, htr⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem39_lock_entry_provenance S Sched x
      (voteTime S (μ + 1)) w e₁ P.hDiv he₁'
  have hμ₁ : μ₀ = μ₁ := by
    have h1 : S.C.t_ (μ₁ + S.C.k) = S.C.t_ (μ₀ + S.C.k) := add_right_cancel (hd₁.symm.trans hd₀)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := t_lt_of_lt S (show μ₀ + S.C.k < μ₁ + S.C.k by omega)
      rw [h1] at this
      exact lt_irrefl _ this
    · have := t_lt_of_lt S (show μ₁ + S.C.k < μ₀ + S.C.k by omega)
      rw [h1] at this
      exact lt_irrefl _ this
  subst hμ₁
  obtain ⟨e₃, -, -, hB₃, hB₃₂⟩ := htr (voteTime S (μ + 1)) (by omega) le_rfl
  have he₁Cw : e₁.B.AncestorEq Cw := ancestorEq_trans (ancestorEq_trans hB₃ hB₃₂) he₂Cw
  -- Lemma 31 at slot `μ₀`
  obtain ⟨hvμ₀, hcμ₀, hfμ₀, hsμ₀, -⟩ := times_eq S μ₀
  obtain ⟨-, hcμ₀1, -, -, -⟩ := times_eq S (μ₀ + 1)
  have hslo : tGAT ≤ supportCutoff S μ₀ :=
    le_trans (tGAT_le_slotStart S (s := μ₀) P.hAnchor (by omega)) (by omega)
  have hcle : supportCutoff S (μ₀ + 1) ≤ supportCutoff S (μ + 1) :=
    supportCutoff_mono S (show μ₀ + 1 ≤ μ + 1 by omega)
  have hc1le : supportCutoff S (μ + 1) ≤ supportCutoff S (μ + 2) :=
    supportCutoff_mono S (show μ + 1 ≤ μ + 2 by omega)
  have hwu : ∀ t : ℕ, supportCutoff S μ₀ ≤ t → t ≤ viewFreeze S μ₀ →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    P.member hu hEnd1 t (by omega) (by omega)
  have hww : ∀ t : ℕ, supportCutoff S μ₀ ≤ t → t ≤ viewFreeze S μ₀ →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    hwin t (by omega) (by omega)
  have hhu : u ∉ Sched.adv ((supportCutoff S (μ₀ + 1) : ℕ) : Int) :=
    (P.member hu hEnd1 _ (by omega) hcle).2
  have hhw : w ∉ Sched.adv ((supportCutoff S (μ₀ + 1) : ℕ) : Int) :=
    (hwin _ (by omega) (le_trans hcle hc1le)).2
  have hcΔ : supportCutoff S μ₀ + Δ S ≤ supportCutoff S (μ + 1) := by
    have := supportCutoff_eq S μ₀
    have := supportCutoff_eq S (μ₀ + 1)
    have := voteTime_succ S μ₀
    omega
  have hc :=
    GoldilocksCorrectness.Statements.Executions.lem31_saved_confirmations_compatible_upTo S Sched x GST
      μ₀ u w Au Aw Cu Cw P.hDiv P.hMono (P.hSync.mono (le_trans hcΔ hEnd1))
      (P.hCatch.mono (le_trans hcΔ hEnd1))
      (P.hRoots.mono (le_trans hcle hEnd1))
      (le_trans P.hGST hslo) hwu hww hhu hhw hAu hSu hAw hCw
  exact compatible_of_ancestorEq_both he₁Cw hX₀Cu (compatible_symm' hc)

/-- **The live locks at the base of a line source are compatible with it.** For a line source
`X₀` of a slot `μ ≥ r * R + 1`, of kind (b) or (c), on the confirmation `C₀` of slot `μ` saved by
`u`'s update `A₀`, when the invariant holds at every slot up to `μ`: every lock entry the
revocation of slot `μ + 1` of a validator `w` honest at the support cutoff of slot `μ + 2` leaves
live is compatible with `X₀`. A lock of a slot `μ₀ ≥ r * R + 1` is a line source of slot `μ₀`, so
`C₀` extends its block; a lock of a slot `μ₀ ≤ r * R` meets a fast `X₀` (Lemma 42) or a slow `X₀`,
whose slow test reads `u`'s confirmation of `μ₀` (Lemmas 37, 39, 40, 31).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem base_locks (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {μ : ℕ}
    (hG : ∀ σ', σ' ≤ μ → LineInv S Sched x r H₂ σ') (hμ : r * S.C.R + 1 ≤ μ)
    (hEnd : supportCutoff S (μ + 2) ≤ tAwakeEnd) {u : V} (hu : u ∈ Hon S Sched μ)
    {A₀ : ACState V} {C₀ X₀ : Block V}
    (hU : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (μ + 1)) u).A
          ((supportCutoff S (μ + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (μ + 1)) u).S)
        ((supportCutoff S (μ + 1) : ℕ) : Int) (μ + 1) = .ok A₀)
    (hC₀ : (stateBefore x (supportCutoff S (μ + 1) + 1) u).A.saved_confirmation μ = some C₀)
    (hX₀C₀ : X₀.AncestorEq C₀)
    (hkind : (X₀ ∈ A₀.fast_blocks ∨
        slow_test S.C (expireLocks (stateBefore x (supportCutoff S (μ + 1)) u).A
          ((supportCutoff S (μ + 1) : ℕ) : Int))
          (fg_to_ac (stateBefore x (supportCutoff S (μ + 1)) u).S) μ X₀ = true) ∨
      r * S.C.R + S.C.k ≤ μ)
    {w : V} (hw : w ∉ Sched.adv ((supportCutoff S (μ + 2) : ℕ) : Int))
    (hsrc : LineSource S Sched x r H₂ μ X₀) :
    ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (μ + 1)) w).A
        ((voteTime S (μ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (μ + 1)) w).S)
        ((voteTime S (μ + 1) : ℕ) : Int) (μ + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (μ + 1)) w).S)
          ((voteTime S (μ + 1) : ℕ) : Int) e = true → e.B.compatible X₀ = true := by
  intro A'' hR e he _
  have hk := S.C.k_ge_two
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := times_eq S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := times_eq S (μ + 1)
  obtain ⟨hv2, hc2, -, -, -⟩ := times_eq S (μ + 2)
  rw [show μ + 1 + 1 = μ + 2 by omega] at hs1
  have hEnd1 : supportCutoff S (μ + 1) ≤ tAwakeEnd := by omega
  have hvE : voteTime S (μ + 1) ≤ tAwakeEnd := by omega
  have hwv : w ∉ Sched.adv ((voteTime S (μ + 1) : ℕ) : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast (show voteTime S (μ + 1) ≤ supportCutoff S (μ + 2)
      by omega)) h)
  have hwin : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (μ + 2) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := P.window hw hEnd
  have hdμ := P.dws (show r * S.C.R ≤ μ by omega)
  have hdμ' := dutyWindowStart_le_voteTime S μ
  -- the fast case: Lemma 42
  by_cases hfast : X₀ ∈ A₀.fast_blocks
  · have hFw : (stateBefore x (voteTime S (μ + 1)) w).S.F.compatible X₀ = true :=
      P.F_compat hG (by omega) (by omega) (by omega) (by omega) hwv hsrc le_rfl
    exact lem42_fast_lock_clears_conflicting_locks_upTo S Sched x GST μ X₀ u w A₀ P.hDiv P.hMono
      (P.hSync.mono hEnd1) (P.hCatch.mono hEnd1) (P.hRoots.mono hEnd1) P.hParent
      (P.gst (by omega)).2.2
      (fun t h1 h2 => P.member1 (by omega) hu hEnd1 t (by have := dutyWindowStart_le_voteTime S (μ + 1); omega) h2)
      (fun t h1 h2 => hwin t (by omega) (by omega)) hU hfast hFw A'' hR e he
  -- the entry `e₁` of `w`'s state `e` was moved from (Lemma 38)
  obtain ⟨e₁, he₁, hl₁, -, hee₁, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A'' _ _ (μ + 1)
      (Nat.le_add_left 1 μ) hR e he
  have he₁' := (Finset.mem_filter.1 he₁).1
  have hl₁' := hl₁
  rw [is_live_iff] at hl₁'
  obtain ⟨μ₀, hd₀, hcut₀, -, hsrc₀⟩ := P.source_lock hwv hvE he₁'
  have hμ₀hi : μ₀ + 1 ≤ μ := by
    by_contra h
    have := supportCutoff_mono S (show μ + 1 ≤ μ₀ + 1 by omega)
    omega
  have huC₀ : u ∈ Hon S Sched μ := hu
  by_cases hnew : r * S.C.R + 1 ≤ μ₀
  · -- a lock of a slot after the fast block's round: a line source, extended by `C₀`
    have h1 := (hG μ le_rfl μ₀ e₁.B (hsrc₀ hnew) hμ₀hi).2.2 u huC₀ C₀ hC₀
    exact compatible_of_ancestorEq_both (ancestorEq_trans hee₁ h1) hX₀C₀
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))
  -- an old lock: `X₀` is slow, and its slow test reads `u`'s confirmation of `μ₀`
  have hslow : slow_test S.C (expireLocks (stateBefore x (supportCutoff S (μ + 1)) u).A
      ((supportCutoff S (μ + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (μ + 1)) u).S) μ X₀ = true := by
    rcases hkind with h | h
    · rcases h with h | h
      · exact absurd h hfast
      · exact h
    · exfalso
      have := GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
        (μ + 1 - S.C.k) μ₀ (voteTime S (μ + 1)) e₁ hd₀ hl₁'.1
        (by rw [show μ + 1 - S.C.k + S.C.k = μ + 1 by omega])
      omega
  exact compatible_of_ancestorEq_compatible hee₁
    (P.old_lock_compat hμ hEnd1 hu hslow hwin he₁' hl₁'.1 hd₀ hμ₀hi)

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- The members of a slot `s ≥ r * R` in the phase are honest active validators and updaters of
it, and the members of slot `s + 1` are members of slot `s`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem members_sets (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R ≤ s) (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    Hon S Sched s ⊆ honestActiveAt S Sched s ∧ Hon S Sched s ⊆ updaterAt S Sched s := by
  have hdw := P.dws hs
  refine ⟨(roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd s P.hMono P.hAwake
    (by omega) hEnd).1, fun u hu => ?_⟩
  have hw := P.member1 hs hu hEnd
  have hd1 : dutyWindowStart S (s + 1) ≤ supportCutoff S (s + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  unfold updaterAt
  rw [Finset.mem_sdiff]
  exact ⟨mem_awakeThroughout_of_forall (fun t h1' h2' => (hw t h1' h2').1), (hw _ hd1 le_rfl).2⟩

/-- The committee of every slot `s ≥ r * R` has more than half of its members in `Hon S Sched s`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem committee (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R ≤ s) :
    (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon S Sched s).card :=
  committee_majority_of_committeeSleepiness S Sched (anchorCW S tGAT) s P.hCommittees
    (le_trans P.hAnchor (slotStart_mono S (by omega)))

/-- **The base of a line source of a slot `μ ≥ r * R + 1`.** When the invariant holds at every
slot up to `μ`, the slot invariant relative to the line source holds at slot `μ + 1`: the votes by
A4 (`lem36c_fast_ancestor_extended_held`), with the frames of `stepFrame_source` and the locks of
`base_locks`; the live locks of slot `μ + 2` by `locks_step_of_clauses` with Lemma 31; the
confirmations by Lemma 78.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem base_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {μ : ℕ}
    (hG : ∀ σ', σ' ≤ μ → LineInv S Sched x r H₂ σ') (hμ : r * S.C.R + 1 ≤ μ)
    (hEnd : supportCutoff S (μ + 2) ≤ tAwakeEnd) {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) :
    HonestChainExtends S Sched x (Hon S Sched (μ + 1)) X (μ + 1) := by
  obtain ⟨u, hu, A₀, C₀, X₀, hU, hS, hC₀, hXX₀, hX₀C₀, hk⟩ := hX
  have hX₀ : LineSource S Sched x r H₂ μ X₀ :=
    ⟨u, hu, A₀, C₀, X₀, hU, hS, hC₀, ancestorEq_refl X₀, hX₀C₀, hk⟩
  have hkind : (X₀ ∈ A₀.fast_blocks ∨
        slow_test S.C (expireLocks (stateBefore x (supportCutoff S (μ + 1)) u).A
          ((supportCutoff S (μ + 1) : ℕ) : Int))
          (fg_to_ac (stateBefore x (supportCutoff S (μ + 1)) u).S) μ X₀ = true) ∨
      r * S.C.R + S.C.k ≤ μ := by
    rcases hk with ⟨h, -⟩ | ⟨-, h⟩ | h
    · omega
    · exact Or.inl h
    · exact Or.inr h
  refine honestChainExtends_of_ancestorEq S Sched x _ X₀ X (μ + 1) hXX₀ ?_
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := times_eq S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := times_eq S (μ + 1)
  obtain ⟨hv2, hc2, -, -, -⟩ := times_eq S (μ + 2)
  rw [show μ + 1 + 1 = μ + 2 by omega] at hs1
  have hEnd1 : supportCutoff S (μ + 1) ≤ tAwakeEnd := by omega
  have hdμ := P.dws (show r * S.C.R ≤ μ by omega)
  have hdμ1 := P.dws (show r * S.C.R ≤ μ + 1 by omega)
  have hd1v := dutyWindowStart_le_voteTime S (μ + 1)
  have hd0v := dutyWindowStart_le_voteTime S μ
  have hds := dutyWindowStart_succ_le_slotStart S μ
  have hmem : ∀ w ∈ Hon S Sched (μ + 1),
      w ∉ Sched.adv ((supportCutoff S (μ + 2) : ℕ) : Int) := by
    intro w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  have hwin : ∀ w ∈ Hon S Sched (μ + 1), ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (μ + 2) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := fun w hw => P.window (hmem w hw) hEnd
  have huw := P.member1 (show r * S.C.R ≤ μ by omega) hu hEnd1
  have hSF : ∀ w ∈ Hon S Sched (μ + 1), StepFrameAt S Sched x X₀ μ w := fun w hw =>
    P.stepFrame_source hG (by omega) hEnd (hmem w hw) hX₀ le_rfl
  have hLk := fun w (hw : w ∈ Hon S Sched (μ + 1)) =>
    P.base_locks hG hμ hEnd hu hU hC₀ hX₀C₀ hkind (hmem w hw) hX₀
  -- the votes of slot `μ + 1` (A4)
  have hVotes : ∀ w ∈ Hon S Sched (μ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (μ + 1)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_w ∈ (stateBefore x (voteTime S (μ + 1)) w).S.T,
        vote = GoldfishVote.mk w (μ + 1) H_w.root ∧ X₀.AncestorEq H_w := by
    intro w hw vote hSend
    exact lem36c_fast_ancestor_extended_held_upTo S Sched x GST μ C₀ X₀ u w A₀ vote P.hDiv P.hMono
      (P.hSync.mono hEnd1) (P.hCatch.mono hEnd1) (P.hRoots.mono hEnd1) P.hParent
      (P.gst (show r * S.C.R ≤ μ by omega)).2.2
      (fun t h1 h2 => huw t (by omega) h2) (fun t h1 h2 => hwin w hw t (by omega) (by omega))
      hU hS hX₀C₀ (hSF w hw).1 (hSF w hw).2.1 (hLk w hw) hSend
  refine ⟨hVotes, fun w hw => ?_, fun v' hv' C'' hC'' => ?_⟩
  · -- the live locks after the revocation of slot `μ + 2`
    refine locks_step_of_clauses S Sched x X₀ μ w P.hDiv (hLk w hw) ?_
      (fun t h1 h2 => hwin w hw t (by have := dutyWindowStart_mono S (show μ + 1 ≤ μ + 2 by omega); omega) (by omega))
    intro Aw hUw Cw hCw
    have hcΔ : supportCutoff S μ + Δ S ≤ tAwakeEnd := by
      have := supportCutoff_eq S μ
      have := supportCutoff_eq S (μ + 1)
      have := voteTime_succ S μ
      omega
    exact compatible_of_ancestorEq_both (ancestorEq_refl Cw) hX₀C₀
      (GoldilocksCorrectness.Statements.Executions.lem31_saved_confirmations_compatible_upTo S Sched x
        GST μ w u Aw A₀ Cw C₀ P.hDiv P.hMono (P.hSync.mono hcΔ) (P.hCatch.mono hcΔ)
        (P.hRoots.mono hEnd1)
        (P.gst (show r * S.C.R ≤ μ by omega)).2.2
        (fun t h1 h2 => hwin w hw t (by omega) (by omega))
        (fun t h1 h2 => huw t (by omega) (by omega))
        (hwin w hw _ (by omega) (by omega)).2 (huw _ (by omega) le_rfl).2 hUw hCw hU hS)
  · -- the confirmations of slot `μ + 1` (Lemma 78)
    obtain ⟨hHA, hUp⟩ := P.members_sets (show r * S.C.R ≤ μ + 1 by omega) hEnd
    exact confirmations_of_votes_clause_upTo S Sched x GST (μ + 1) (Hon S Sched (μ + 1)) X₀ v' P.hDiv
      P.hMono (P.hSync.mono hEnd1) (P.hCatch.mono hEnd1) (P.hRoots.mono hEnd1) P.hParent P.hOwner
      (P.gst (show r * S.C.R ≤ μ + 1 by omega)).2.1 hHA (P.committee (by omega)) hVotes
      (hUp hv') (hSF v' hv').2.2 C'' hC''

/-- **The step of a line source.** When the invariant holds at every slot up to `σ`, the slot
invariant relative to a line source of a slot at most `σ` at slot `σ` gives it at slot `σ + 1`
(`lem79_step_sets`, the frames of `stepFrame_source`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem step_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ)
    (hInv : HonestChainExtends S Sched x (Hon S Sched σ) X σ) :
    HonestChainExtends S Sched x (Hon S Sched (σ + 1)) X (σ + 1) := by
  have hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ _)) hEnd
  have hmem : ∀ w ∈ Hon S Sched (σ + 1),
      w ∉ Sched.adv ((supportCutoff S (σ + 2) : ℕ) : Int) := by
    intro w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  have hSF : ∀ w ∈ Hon S Sched (σ + 1), StepFrameAt S Sched x X σ w := fun w hw =>
    P.stepFrame_source hG hσ hEnd (hmem w hw) hX hμ
  have hvoters : ∀ s : ℕ, r * S.C.R ≤ s → supportCutoff S (s + 1) ≤ tAwakeEnd →
      ∀ u ∈ S.P.committee s ∩ Hon S Sched s, u ∈ Hon S Sched s ∧ u ∈ S.P.committee s ∧
        ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s ∧
          ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
              x[i + 1].sent - x[i].sent := by
    intro s hs hE u hu
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x s u P.hDiv P.hMono
        ((P.members_sets hs hE).1 hH) hK
    exact ⟨hH, hK, vote, hvi, hvs, i, hl, hsent⟩
  exact lem79_step_sets_upTo S Sched x GST σ (Hon S Sched σ) (Hon S Sched (σ + 1))
    (fun s => S.P.committee s ∩ Hon S Sched s) X P.hDiv P.hMono (P.hSync.mono hEnd1)
    (P.hCatch.mono hEnd1) (P.hRoots.mono hEnd1) P.hParent P.hOwner (P.gst hσ).2.1 hInv
    (roundMembers_mono S Sched (σ + 1) (σ + 2) tAwakeEnd P.hMono (Nat.le_succ _) hEnd).1
    (fun u hu => P.member0 hσ hu hEnd1) (fun u hu => P.member0 (by omega) hu hEnd)
    (hvoters σ hσ hEnd1) (hvoters (σ + 1) (by omega) hEnd)
    (fun w _ => (counting_of_committee_majority S Sched x σ (voteTime S (σ + 1)) (Hon S Sched σ) w
      (P.committee hσ)).2.2)
    (fun v' _ => (counting_of_committee_majority S Sched x (σ + 1) (supportCutoff S (σ + 2))
      (Hon S Sched (σ + 1)) v' (P.committee (by omega))).2.1)
    (fun w hw => (hSF w hw).1) (fun w hw => (hSF w hw).2.1) (fun w hw => (hSF w hw).2.2)

/-- **The line invariant at every slot of the phase.** At every slot `σ` whose support cutoff of
slot `σ + 1` is at most `tAwakeEnd`, the slot invariant holds relative to every line source of a
slot before `σ`: by strong induction on `σ`, the base of each source at the slot after its own
(A5 for kind (a), `base_source` otherwise), and `step_source` after.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem lineInv_all (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') :
    ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ tAwakeEnd → LineInv S Sched x r H₂ σ := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro hEnd μ X hX hμσ
    obtain ⟨σ₀, rfl⟩ : ∃ σ₀, σ = σ₀ + 1 := ⟨σ - 1, by omega⟩
    have hG : ∀ σ', σ' ≤ σ₀ → LineInv S Sched x r H₂ σ' := fun σ' h =>
      ih σ' (by omega) (le_trans (supportCutoff_mono S (by omega)) hEnd)
    have hEnd' : supportCutoff S (σ₀ + 2) ≤ tAwakeEnd := hEnd
    have hs := hX.slot_ge
    rcases Nat.lt_or_eq_of_le (show μ ≤ σ₀ by omega) with hlt | heq
    · exact P.step_source hG (by omega) hEnd' hX (by omega)
        (hG σ₀ le_rfl μ X hX (by omega))
    · subst heq
      by_cases hμ : r * S.C.R + 1 ≤ μ
      · exact P.base_source hG hμ hEnd' hX
      · obtain ⟨u, hu, A₀, C₀, X₀, hU, -, -, hXX₀, -, hk⟩ := hX
        have hμR : μ = r * S.C.R := by omega
        rcases hk with ⟨-, hf, hh⟩ | ⟨h, -⟩ | h
        · subst hμR
          have huv : u ∉ Sched.adv ((aR S r : ℕ) : Int) := by
            unfold Hon roundMembers at hu
            exact (Finset.mem_sdiff.1 hu).2
          exact honestChainExtends_of_ancestorEq S Sched x _ X₀ X _ hXX₀
            (GoldilocksCorrectness.Proofs.Executions.fast_block_base_upTo S Sched x GST tGAT tAwakeEnd r
              H₂ u X₀ A₀ P.hDiv P.hMono
              (P.hSync.mono (le_trans (supportCutoff_mono S (by omega)) hEnd'))
              (P.hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hEnd'))
              (P.hRoots.mono hEnd') P.hParent
              P.hOwner P.hU
              P.hGST P.hThird P.hAwake P.hCommittees P.hAnchor hEnd' P.hOld huv hU hf hh)
        · omega
        · have := S.C.k_ge_two
          omega

end PartAHypsUpTo

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- The line invariant at every slot up to `s`, when the support cutoff of slot `s + 2` is in the
phase.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem lineInv_upto (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd) :
    ∀ σ', σ' ≤ s → LineInv S Sched x r H₂ σ' := fun σ' h =>
  P.lineInv_all σ' (le_trans (supportCutoff_mono S (by omega)) hEnd)

/-- A fast block of an honest update at the action time of a round `r' ≥ r` is a line source of
the round's first slot: of kind (b) when `r' > r`; when `r' = r`, of kind (a) at the height
`H₂ + 1`, and an ancestor of `L` at a lower height (A2 bounds the height by `H₂ + 1`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem source_later (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {r' : ℕ} {u : V}
    {X : Block V} {A_u : ACState V} (hr' : r ≤ r') (hu : u ∉ Sched.adv ((aR S r' : ℕ) : Int))
    (hUpdate_u : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r') u).A ((aR S r' : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r') u).S) ((aR S r' : ℕ) : Int) (r' * S.C.R + 1) =
          .ok A_u)
    (hFast_u : X ∈ A_u.fast_blocks) (hEnd : supportCutoff S (r' * S.C.R + 1) ≤ tAwakeEnd) :
    LineSource S Sched x r H₂ (r' * S.C.R) X := by
  have huH : u ∈ Hon S Sched (r' * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hu⟩
  have hU : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).A
        ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).S)
      ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int) (r' * S.C.R + 1) = .ok A_u := hUpdate_u
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved S.C S.P _ A_u _ _
      (r' * S.C.R + 1) X (Nat.le_add_left 1 _) hU hFast_u
  rw [Nat.add_sub_cancel] at hC₀
  have hrR : r * S.C.R ≤ r' * S.C.R := Nat.mul_le_mul_right _ hr'
  have hw := P.member1 hrR huH hEnd
  have hst := state_saved_of_update S Sched x (r' * S.C.R) u A_u P.hDiv P.hMono hw hU
  rcases Nat.lt_or_eq_of_le hr' with hlt | heq
  · refine ⟨u, huH, A_u, C₀, X, hU, hC₀, hst.trans hC₀, ancestorEq_refl X, hXC₀,
      Or.inr (Or.inl ⟨?_, Or.inl hFast_u⟩)⟩
    have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
    have h2 := S.C.R_ge_two
    rw [Nat.succ_mul] at h1
    omega
  · subst heq
    -- `X` is held by `u` before `a_r`, so its height is at most `H₂ + 1` (A2)
    have hCT := saved_confirmation_mem_T_supportCutoff S Sched x (r * S.C.R) u C₀ P.hDiv P.hMono
      hw (hst.trans hC₀)
    have hXT := (stateBefore_grows x P.hDiv u (supportCutoff_mono S (Nat.le_succ _))).1
      (ancestors_mem_T_of_exec S Sched x _ u C₀ X hCT hXC₀)
    have hle := held_height_le_before_action S Sched x tAwakeEnd r H₂ (aR S r) u X P.hU
      P.hThird P.hOld le_rfl hEnd hXT
    by_cases hh : (chainStateOf S.C X).h = H₂ + 1
    · exact ⟨u, huH, A_u, C₀, X, hU, hC₀, hst.trans hC₀, ancestorEq_refl X, hXC₀,
        Or.inl ⟨rfl, hFast_u, hh⟩⟩
    · have hlt : (chainStateOf S.C X).h < H₂ + 1 := by unfold Height at *; omega
      obtain ⟨u', hu', A₀', C₀', X₀', -, -, hC₀', hLX₀', hX₀C₀', -⟩ := P.source_L hEnd
      have hcΔ : supportCutoff S (r * S.C.R) + Δ S ≤ tAwakeEnd := by
        have := supportCutoff_eq S (r * S.C.R)
        have := supportCutoff_eq S (r * S.C.R + 1)
        have := voteTime_succ S (r * S.C.R)
        omega
      have hc := lem32_saved_confirmations_compatible_state_upTo S Sched x GST (r * S.C.R) u u' C₀ C₀'
        P.hDiv P.hMono (P.hSync.mono hcΔ) (P.hCatch.mono hcΔ) (P.hRoots.mono hEnd)
        (P.gst le_rfl).2.2 hw
        (P.member1 le_rfl hu' hEnd) (hst.trans hC₀) hC₀'
      have hXL := compatible_of_ancestorEq_both hXC₀ (ancestorEq_trans hLX₀' hX₀C₀') hc
      rcases (compatible_iff _ _).1 hXL with h | h
      · exact (P.source_L hEnd).anc h
      · exfalso
        have := chainStateOf_height_mono S.C h
        rw [P.hL] at this
        unfold Height at *
        omega

end PartAHypsUpTo

end GoldilocksCorrectness.Proofs.Executions

