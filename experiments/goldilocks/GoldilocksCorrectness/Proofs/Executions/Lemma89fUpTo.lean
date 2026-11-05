module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Proofs.Executions.PhaseChainUpTo

@[expose] public section

/-!
# `Lemma89f.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89f.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `confirmations_of_votes_clause`, `FrontHyps`, `window`, `anti`, `gst`, `honestActive`,
  `updater`, `voters`, `rootsAt`, `front_carry_step`, `front_lock_base`, `liveLockAncestors_succ`,
  `front_step_frames`, `front_locks_chain`, `lem89fq_front`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_le_voteTime dutyWindowStart_mono one_le_Δ slotStart_mono supportCutoff_eq
  supportCutoff_mono voteTime_eq voteTime_mono voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible voters_count_lt_of_committee_majority)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The confirmations of a slot extend a block its votes extend (Lemma 78).** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST`, a root names one block among what honest
validators hold, a block reaches a validator only once it holds the parent, and nobody votes in an
honest validator's name: if `GST` is at most the vote time of slot `s`; `Hon` is a set of honest
active validators of slot `s` with more than half of the committee of slot `s`; every slot-`s` vote
of a member of `Hon` is its vote for a block it holds that is `C` or a descendant of `C`; `v` is an
updater of slot `s`; and `v`'s finalized block before the support cutoff of slot `s + 1` is
compatible with `C` — then `C` is an ancestor of, or equal to, the confirmation of slot `s` that
`v` holds right after that cutoff.

Why: `chainInvFor_updater_confirmation`'s proof, which reads only the first clause of the
invariant.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the voters; `C`: the block; `v`: the updater.

Roots name blocks until `supportCutoff S s`: Lemma 78 at slot `s` reads blocks held up to it.

Restated with the delivery premises up to `supportCutoff S s`: Lemma 78 at slot `s` reads deliveries due by then (`lem78_update_confirmation_extends_voter_majority_chain_upTo`). -/
theorem confirmations_of_votes_clause_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hon : Finset V) (C : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHon : Hon ⊆ honestActiveAt S Sched s)
    (hCommittee : |S.P.committee s| < 2 * |S.P.committee s ∩ Hon|)
    (hC1 : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s) u).S.T,
        vote = GoldfishVote.mk u s H_u.root ∧ C.AncestorEq H_u)
    (hv : v ∈ updaterAt S Sched s)
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible C = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C.AncestorEq C' := by
  have hdc : dutyWindowStart S s ≤ supportCutoff S (s + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x s (S.P.committee s ∩ Hon) C hDiv hMono
    (fun u hu => ⟨hHon (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (fun u hu => hC1 u (Finset.mem_inter.1 hu).2)
  exact GoldilocksCorrectness.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo
    S Sched x GST s (S.P.committee s ∩ Hon) H C v hDiv hMono hSync hCatch hRoots hParent
    hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (honestActiveAt_window S Sched s u hMono (hHon (Finset.mem_inter.1 hu).2)
        (supportCutoff S (s + 1)) hdc le_rfl).2, (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x _ v s)
      (committee_sdiff_lt _ _ hCommittee))
    (updaterAt_window S Sched s v hMono hv) hF

/-- `FrontHyps S Sched x GST tGAT tAwakeEnd s_w s' Hon`: the hypotheses of `lem89fq_front` the
kit theorems of this file read, but `hs'` and `hRootsOn`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `s_w`: a slot whose duty window starts
  at or after `tGAT`; `s'`: the slot of the conclusion; `Hon`: the member sets.

Restated with the delivery premises up to `supportCutoff S s'`: the kit theorems of this file read Lemmas 45b, 12, 78 and 79 and the phase step at slots at most `s'`, whose deliveries are due by then, as `hRoots` is. -/
structure FrontHypsUpTo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V) : Prop where
  /-- Every time is reached. -/
  hDiv : TimeDiverges x.toTrace
  /-- Corruption is permanent. -/
  hMono : Sched.MonotoneCorruption
  /-- Blocks and Goldfish votes reach an awake receiver within `Δ` after `GST`. -/
  hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s')
  /-- A waking receiver catches up within `Δ` after `GST`. -/
  hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s')
  /-- A root names one block among what honest validators hold, until the support cutoff of
  slot `s'`. -/
  hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s')
  /-- A block reaches a validator only once it holds the parent. -/
  hParent : ParentHeldAtDelivery S Sched x
  /-- Nobody votes in an honest validator's name. -/
  hOwner : VotesCastByOwner S Sched x
  /-- The network is synchronous from `tGAT` on. -/
  hGST : GST ≤ tGAT
  /-- The set of slot `s₁ + 1` is inside that of slot `s₁`, from `s_w` to before `s'`. -/
  hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁
  /-- Every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`. -/
  hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
    v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int)
  /-- Every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then. -/
  hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
    ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int)
  /-- The committee of every slot from `s_w + k` to `s'` has its majority in the slot's set. -/
  hCommittees : ∀ s₁, s_w + S.C.k ≤ s₁ → s₁ ≤ s' →
    (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card
  /-- The duty window of slot `s_w` starts at or after `tGAT`. -/
  hsw : tGAT ≤ dutyWindowStart S s_w
  /-- The support cutoff of slot `s' + 1` is at most `tAwakeEnd`. -/
  hEnd : supportCutoff S (s' + 1) ≤ tAwakeEnd
  /-- At every slot `s₁` from `s_w + k − 1` to `s' − 1`, every member of `Hon (s₁ + 1)` satisfies
  `StepFrameAt` relative to every confirmation a member of `Hon (σ + 1)` saved for a slot `σ`
  from `s_w + k − 1` to `s₁`. -/
  hFrame : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
    ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
      ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C s₁ w

namespace FrontHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}

/-- The members' windows, read off the bundle (`front_member_window`).

The variables:
- `H`: the bundle; `s₁`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem window (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s₁ : ℕ) (h1 : s_w ≤ s₁)
    (h2 : s₁ ≤ s') : ∀ v ∈ Hon s₁, ∀ t : ℕ, dutyWindowStart S s₁ ≤ t →
      t ≤ supportCutoff S (s₁ + 1) → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
  fun v hv => front_member_window S Sched tGAT tAwakeEnd s_w s' s₁ Hon v H.hMono H.hHon H.hAwake
    H.hsw H.hEnd h1 h2 hv

/-- The member sets shrink over the range, read off the bundle (`front_hon_anti`).

The variables:
- `H`: the bundle; `a ≤ b`: the two slots.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem anti (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (a b : ℕ) (ha : s_w ≤ a)
    (hab : a ≤ b) (hb : b ≤ s') : Hon b ⊆ Hon a :=
  front_hon_anti s_w s' Hon H.hHonMono a b ha hab hb

/-- `GST` is at most the vote time of every slot from `s_w` on.

The variables:
- `H`: the bundle; `s`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem gst (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s : ℕ) (h : s_w ≤ s) :
    GST ≤ voteTime S s := by
  have h1 := H.hGST
  have h2 := H.hsw
  have h3 := dutyWindowStart_mono S h
  have h4 := dutyWindowStart_le_voteTime S s
  omega

/-- The members of a slot are honest active validators of it.

The variables:
- `H`: the bundle; `s₁`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem honestActive (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s₁ : ℕ)
    (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') : Hon s₁ ⊆ honestActiveAt S Sched s₁ := by
  intro u hu
  have hd0 : dutyWindowStart S s₁ ≤ supportCutoff S (s₁ + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  unfold honestActiveAt activeAt
  rw [Finset.mem_sdiff]
  exact ⟨mem_awakeThroughout_of_forall (fun t h1' h2' => (H.window s₁ h1 h2 u hu t h1' h2').1),
    (H.window s₁ h1 h2 u hu _ hd0 le_rfl).2⟩

/-- The members of a slot are updaters of it.

The variables:
- `H`: the bundle; `s₁`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem updater (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s₁ : ℕ)
    (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') : Hon s₁ ⊆ updaterAt S Sched s₁ := by
  intro u hu
  have hd1 : dutyWindowStart S (s₁ + 1) ≤ supportCutoff S (s₁ + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  have hdm := dutyWindowStart_mono S (Nat.le_add_right s₁ 1)
  unfold updaterAt
  rw [Finset.mem_sdiff]
  exact ⟨mem_awakeThroughout_of_forall (fun t h1' h2' =>
      (H.window s₁ h1 h2 u hu t (le_trans hdm h1') h2').1),
    (H.window s₁ h1 h2 u hu _ (le_trans hdm hd1) le_rfl).2⟩

/-- Every member of the committee of a slot in the slot's set put a slot-`s₁` Goldfish vote on the
wire at its tick at the vote time of slot `s₁` (`honest_votes_of_window`).

The variables:
- `H`: the bundle; `s₁`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem voters (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s₁ : ℕ)
    (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') :
    ∀ u ∈ S.P.committee s₁ ∩ Hon s₁, u ∈ Hon s₁ ∧ u ∈ S.P.committee s₁ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₁ ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₁) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent := by
  intro u hu
  obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
  have hΔ := one_le_Δ S
  have hdv := dutyWindowStart_le_voteTime S s₁
  have hvc : voteTime S s₁ ≤ supportCutoff S (s₁ + 1) := by
    have := supportCutoff_eq S (s₁ + 1)
    have := voteTime_succ S s₁
    omega
  obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ := honest_votes_of_window S Sched x s₁ u H.hDiv H.hMono
    (fun t h1' h2' => (H.window s₁ h1 h2 u huH t h1' (le_trans h2' hvc)).1)
    (H.window s₁ h1 h2 u huH _ hdv hvc).2 hK
  exact ⟨huH, hK, vote, hvi, hvs, i, hl, hsent⟩

/-- Roots name blocks until every time at most the support cutoff of slot `s'`, read off the
bundle.

The variables:
- `H`: the bundle; `t`: the time.

Restated with the delivery premises up to `supportCutoff S s'`: the bundle `FrontHypsUpTo` carries them; this reader reads none of them. -/
theorem rootsAt (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) {t : ℕ}
    (ht : t ≤ supportCutoff S s') : RootsNameBlocksUntil S Sched x t :=
  H.hRoots.mono ht

end FrontHypsUpTo

/-- **The carry, one slot.** Under the bundle, at a slot `s₁` from `s_w + k` with `s₁ + 1 ≤ s'`:
when `StepFrameAt S Sched x B s₁ w` holds at every member `w` of `Hon (s₁ + 1)`,
`HonestChainExtends` at slot `s₁` for `Hon s₁` relative to `B` gives it at slot `s₁ + 1` for
`Hon (s₁ + 1)`.

Why: `lem79_step_sets`, with the honest voters `S.P.committee s ∩ Hon s` of each slot and the
counting from the committee majorities (`counting_of_committee_majority`).

The variables:
- `H`: the bundle; `s₁`: the slot; `B`: the block.

Restated with the delivery premises up to `supportCutoff S s'`: through the bundle `FrontHypsUpTo`; `lem79_step_sets_upTo` at slot `s₁ < s'` reads deliveries due by `supportCutoff S (s₁ + 1)`. -/
theorem front_carry_step_upTo {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
    {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s₁ : ℕ) (h1 : s_w + S.C.k ≤ s₁)
    (h2 : s₁ + 1 ≤ s') (B : Block V)
    (hSt : ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x B s₁ w)
    (hInv : HonestChainExtends S Sched x (Hon s₁) B s₁) :
    HonestChainExtends S Sched x (Hon (s₁ + 1)) B (s₁ + 1) :=
  lem79_step_sets_upTo S Sched x GST s₁ (Hon s₁) (Hon (s₁ + 1)) (fun s => S.P.committee s ∩ Hon s) B
    H.hDiv H.hMono (H.hSync.mono (supportCutoff_mono S (by omega)))
    (H.hCatch.mono (supportCutoff_mono S (by omega))) (H.rootsAt (supportCutoff_mono S (by omega)))
    H.hParent H.hOwner (H.gst s₁ (by omega)) hInv (H.hHonMono s₁ (by omega) (by omega))
    (H.window s₁ (by omega) (by omega))
    (H.window (s₁ + 1) (by omega) (by omega))
    (H.voters s₁ (by omega) (by omega))
    (H.voters (s₁ + 1) (by omega) (by omega))
    (fun w _ => (counting_of_committee_majority S Sched x s₁ (voteTime S (s₁ + 1)) (Hon s₁) w
      (H.hCommittees s₁ (by omega) (by omega))).2.2)
    (fun v _ => (counting_of_committee_majority S Sched x (s₁ + 1) (supportCutoff S (s₁ + 2))
      (Hon (s₁ + 1)) v (H.hCommittees (s₁ + 1) (by omega) (by omega))).2.1)
    (fun w hw => (hSt w hw).1) (fun w hw => (hSt w hw).2.1) (fun v hv => (hSt v hv).2.2)

/-- **The base, one lock.** Under the bundle, with `b₀ + 2 = s_w + 2k` and `b₀ ≤ s'`: for every
lock entry `e` that a member `u` of `Hon b₀` holds live before the vote time of slot `b₀ + 1`,
`HonestChainExtends S Sched x (Hon b₀) e.B b₀` holds.

Why: `e` was added, as an entry `e₀` on `u`'s saved confirmation `C'` of a slot `σ` or an ancestor
of it, by `u`'s update of slot `σ + 1`, and `e`'s block is an ancestor of `e₀`'s (Lemma 39); `e`
being live at the vote time of slot `b₀ + 1 = s_w + 2k − 1` makes `σ ≥ s_w + k − 1` (Lemma 41),
and the update ran before that vote time, so `σ + 1 ≤ b₀`. At slot `σ + 1`: every member's vote
extends `e₀`'s block (Lemma 45b, its frame conditions from `hFrame` at slot `σ` relative to `C'`,
`GST` before the vote time of slot `σ + 1 − k ≥ s_w`); those votes are a majority of the
committee of slot `σ + 1` for blocks on `e`'s chain, and every member's finalized block before the
support cutoff of slot `σ + 2` is compatible with `e`'s block (`hFrame` at slot `σ` relative to
`C'`, its third conjunct), so every lock entry the revocation of slot `σ + 2` leaves at a member
is compatible with `e`'s block (`locks_clause_of_votes`: Lemma 12, then Lemma 5); no two live
locks are compared, and no lock older than slot `σ` is read. Every member's confirmation of slot
`σ + 1` extends `e`'s block (Lemma 78, `hFrame`'s third conjunct). Then `front_carry_step` at
every slot from `σ + 1` to `b₀ − 1`, `hFrame` relative to `C'`.

The variables:
- `H`: the bundle; `b₀`: the base slot; `u`: the holder; `e`: the lock entry.

Restated with the delivery premises up to `supportCutoff S s'`: through the bundle `FrontHypsUpTo`; Lemmas 45b, 12 and 78 at the slot `σ + 1 ≤ s'` read deliveries due by the support cutoff of that slot. -/
theorem front_lock_base_upTo {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
    {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (b₀ : ℕ)
    (hb₀ : b₀ + 2 = s_w + 2 * S.C.k) (hb : b₀ ≤ s') (u : V) (hu : u ∈ Hon b₀) (e : LockEntry V)
    (he : e ∈ (stateBefore x (voteTime S (b₀ + 1)) u).A.lock_entries)
    (hlive : is_live (fg_to_ac (stateBefore x (voteTime S (b₀ + 1)) u).S)
      ((voteTime S (b₀ + 1) : ℕ) : Int) e = true) :
    HonestChainExtends S Sched x (Hon b₀) e.B b₀ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  -- where `e` comes from (Lemma 39)
  obtain ⟨σ, hd, hcut, -, A', hA', e₀, he₀, hd₀, he₀T, -, ⟨C', hC', he₀C'⟩, -, htr⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem39_lock_entry_provenance S Sched x
      (voteTime S (b₀ + 1)) u e H.hDiv he
  have hlive' := hlive
  simp only [is_live_iff] at hlive'
  obtain ⟨hlt, hTr⟩ := hlive'
  -- the slot of the lock is from `s_w + k − 1` to `b₀ − 1`
  have hσlo : s_w + S.C.k - 1 ≤ σ :=
    GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S (s_w + S.C.k - 1) σ
      (voteTime S (b₀ + 1)) e hd hlt (by rw [show s_w + S.C.k - 1 + S.C.k = b₀ + 1 by omega])
  have hσhi : σ + 1 ≤ b₀ := by
    by_contra h
    have hm := slotStart_mono S (show b₀ + 1 ≤ σ + 1 by omega)
    have h1 := voteTime_eq S (b₀ + 1)
    have h2 := supportCutoff_eq S (σ + 1)
    have h3 := voteTime_eq S (σ + 1)
    omega
  -- `u`'s saved confirmation of slot `σ`
  obtain ⟨-, -, A'', hA'', hsave, -⟩ :=
    GoldilocksCorrectness.Statements.Executions.update_state_of_lock_entry S Sched x
      (voteTime S (b₀ + 1)) σ u e H.hDiv he hd hcut
  have hAA : A'' = A' := by
    rw [hA''] at hA'
    exact Except.ok.inj hA'
  have hsv : (stateBefore x (supportCutoff S (σ + 1) + 1) u).A.saved_confirmation σ = some C' := by
    rw [hsave, hAA]
    exact hC'
  have hu₁ : u ∈ Hon (σ + 1) := H.anti (σ + 1) b₀ (by omega) hσhi hb hu
  -- the frames relative to `C'`
  have hFr : ∀ s₁, σ ≤ s₁ → s₁ < s' → ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C' s₁ w :=
    fun s₁ h1 h2 => H.hFrame s₁ (by omega) h2 σ hσlo h1 u hu₁ C' hsv
  -- `e`'s block is an ancestor of the added entry's
  obtain ⟨e₁, -, -, hB₁, hB₁₀⟩ := htr (voteTime S (b₀ + 1)) hcut le_rfl
  have heB₀ : e.B.AncestorEq e₀.B := ancestorEq_trans hB₁ hB₁₀
  have heC' : e.B.AncestorEq C' := ancestorEq_trans heB₀ he₀C'
  -- the times
  have hc1 := supportCutoff_eq S (σ + 1)
  have hc2 := supportCutoff_eq S (σ + 1 + 1)
  have hv2 := voteTime_succ S (σ + 1)
  have hdm := dutyWindowStart_mono S (Nat.le_add_right (σ + 1) 1)
  -- clause 1 at slot `σ + 1`: Lemma 45b
  have hc1' : ∀ w ∈ Hon (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (σ + 1)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_w ∈ (stateBefore x (voteTime S (σ + 1)) w).S.T,
        vote = GoldfishVote.mk w (σ + 1) H_w.root ∧ e.B.AncestorEq H_w := by
    intro w hw vote hSend
    have hF := stepFrameAt_of_ancestorEq S Sched x C' e₀.B σ w he₀C'
      (hFr σ le_rfl (by omega) w hw)
    obtain ⟨H_w, hHT, hvt, hBH⟩ := lem45b_honest_vote_extends_lock_held_upTo S Sched x GST σ u w A' e₀
      vote H.hDiv H.hMono (H.hSync.mono (supportCutoff_mono S (by omega)))
      (H.hCatch.mono (supportCutoff_mono S (by omega)))
      (H.rootsAt (supportCutoff_mono S (by omega))) H.hParent
      (by have := H.gst (σ + 1 - S.C.k) (by omega); have := supportCutoff_eq S (σ + 1 - S.C.k)
          omega)
      (fun t h1 h2 => H.window (σ + 1) (by omega) (by omega) u hu₁ t h1 (by omega))
      (fun t h1 h2 => H.window (σ + 1) (by omega) (by omega) w hw t h1 (by omega))
      hA' he₀ (hd₀.trans hd) hF.1 hF.2.1 hSend
    exact ⟨H_w, hHT, hvt, ancestorEq_trans heB₀ hBH⟩
  have hbase : HonestChainExtends S Sched x (Hon (σ + 1)) e.B (σ + 1) := by
    refine ⟨hc1', fun w hw A₂ hR e₂ he₂ _ => ?_, fun v hv C'' hC'' => ?_⟩
    · -- clause 2: `locks_clause_of_votes_upTo` against the members' votes of slot `σ + 1`
      obtain ⟨Hv, hHv⟩ := voters_of_votes_clause S Sched x (σ + 1)
        (S.P.committee (σ + 1) ∩ Hon (σ + 1)) e.B H.hDiv H.hMono
        (fun u' hu' => ⟨H.honestActive (σ + 1) (by omega) (by omega) (Finset.mem_inter.1 hu').2,
          (Finset.mem_inter.1 hu').1⟩)
        (fun u' hu' => hc1' u' (Finset.mem_inter.1 hu').2)
      exact locks_clause_of_votes_upTo S Sched x GST (σ + 1) (Hon (σ + 1)) e.B Hv H.hDiv H.hMono
        (H.hSync.mono (supportCutoff_mono S (by omega)))
        (H.hCatch.mono (supportCutoff_mono S (by omega)))
        (H.rootsAt (supportCutoff_mono S (by omega))) H.hParent
        H.hOwner (H.gst (σ + 1) (by omega))
        (fun v hv t h1 h2 => H.window (σ + 1) (by omega) (by omega) v hv t h1 (by omega))
        (H.hCommittees (σ + 1) (by omega) (by omega)) hHv
        (fun v hv => (stepFrameAt_of_ancestorEq S Sched x C' e.B σ v heC'
          (hFr σ le_rfl (by omega) v hv)).2.2)
        w hw A₂ hR e₂ he₂
    · -- clause 3: Lemma 78
      have hF := (stepFrameAt_of_ancestorEq S Sched x C' e.B σ v heC'
        (hFr σ le_rfl (by omega) v hv)).2.2
      exact confirmations_of_votes_clause_upTo S Sched x GST (σ + 1) (Hon (σ + 1)) e.B v H.hDiv
        H.hMono (H.hSync.mono (supportCutoff_mono S (by omega)))
        (H.hCatch.mono (supportCutoff_mono S (by omega)))
        (H.rootsAt (supportCutoff_mono S (by omega))) H.hParent
        H.hOwner (H.gst _ (by omega)) (H.honestActive (σ + 1) (by omega) (by omega))
        (H.hCommittees (σ + 1) (by omega) (by omega)) hc1'
        (H.updater (σ + 1) (by omega) (by omega) hv) hF C'' hC''
  -- the carry to slot `b₀`
  have key : ∀ d, σ + 1 + d ≤ b₀ →
      HonestChainExtends S Sched x (Hon (σ + 1 + d)) e.B (σ + 1 + d) := by
    intro d
    induction d with
    | zero => intro _; exact hbase
    | succ d ih =>
        intro hd'
        rw [show σ + 1 + (d + 1) = σ + 1 + d + 1 by omega]
        exact front_carry_step_upTo H (σ + 1 + d) (by omega) (by omega) e.B
          (fun w hw => stepFrameAt_of_ancestorEq S Sched x C' e.B _ w heC'
            (hFr (σ + 1 + d) (by omega) (by omega) w hw))
          (ih (by omega))
  have := key (b₀ - (σ + 1)) (by omega)
  rwa [show σ + 1 + (b₀ - (σ + 1)) = b₀ by omega] at this

/-- **The live lock blocks of the next slot.** Under the bundle, at a slot `s₁` from `s_w` with
`s₁ + 1 ≤ s'`: a block on the chain of a live lock a member of `Hon (s₁ + 1)` holds before the vote
time of slot `s₁ + 2` is on the chain of a live lock a member of `Hon s₁` holds before the vote
time of slot `s₁ + 1`, or is an ancestor of, or equal to, a member's confirmation of slot `s₁`.

Why: `live_lock_entry_source` at the vote time of slot `s₁ + 2`: the entry is on the holder's own
confirmation of slot `s₁`, or on an ancestor of an entry the revocation of slot `s₁ + 1` left live,
itself on an ancestor of a live entry of its input (Lemma 38); the holder is a member of `Hon s₁`.

The variables:
- `H`: the bundle; `s₁`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: through the bundle `FrontHypsUpTo`; the proof reads none of them. -/
theorem liveLockAncestors_succ_upTo {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (s₁ : ℕ) (h1 : s_w ≤ s₁)
    (h2 : s₁ + 1 ≤ s') (C : Block V)
    (hC : liveLockAncestors S Sched x (Hon (s₁ + 1)) (s₁ + 1) C) :
    liveLockAncestors S Sched x (Hon s₁) s₁ C ∨ ∃ v ∈ Hon (s₁ + 1), ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s₁ + 1) + 1) v).A.saved_confirmation s₁ = some C' ∧
      C.AncestorEq C' := by
  obtain ⟨u, hu, e, he, hl, hCe⟩ := hC
  have hl' := hl
  simp only [is_live_iff] at hl'
  have hΔ := one_le_Δ S
  have hc1 := supportCutoff_eq S (s₁ + 1)
  have hc2 := supportCutoff_eq S (s₁ + 1 + 1)
  have hv2 := voteTime_succ S (s₁ + 1)
  rcases live_lock_entry_source S Sched x s₁ (voteTime S (s₁ + 1 + 1)) u H.hDiv
      (fun t h1' h2' => H.window (s₁ + 1) (by omega) h2 u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1') (by omega)) (by omega)
      le_rfl e he hl'.1 with ⟨C', hC', heC'⟩ | ⟨A₃, hR₃, e', he', hl₃, hee'⟩
  · exact Or.inr ⟨u, hu, C', hC', ancestorEq_trans hCe heC'⟩
  · obtain ⟨e₁, he₁, hl₁, -, he'₁, -⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A₃ _ _
        (s₁ + 1) (Nat.le_add_left 1 s₁) hR₃ e' he'
    exact Or.inl ⟨u, H.hHonMono s₁ h1 (by omega) hu, e₁, (Finset.mem_filter.1 he₁).1, hl₁,
      ancestorEq_trans hCe (ancestorEq_trans hee' he'₁)⟩

/-- **The frames of the step.** Under the bundle, with `b₀ + 2 = s_w + 2k`, at a slot `s₁` with
`b₀ ≤ s₁ < s'`: for every block on the chain of a live lock a member of `Hon s₁` holds before the
vote time of slot `s₁ + 1`, and every confirmation of slot `s₁` a member of `Hon (s₁ + 1)` holds,
`StepFrameAt S Sched x C s₁ w` holds at every member `w` of `Hon (s₁ + 1)`.

Why: a live lock at the vote time of slot `s₁ + 1 ≥ s_w + 2k − 1` is of a slot `σ ≥ s_w + k − 1`
(Lemma 41) on its holder's confirmation of slot `σ`, or an ancestor of it
(`lock_entry_confirmation`), with `σ + 1 ≤ s₁`; `hFrame` at slot `s₁` relative to that
confirmation, or to the member's confirmation of slot `s₁`, and `stepFrameAt_of_ancestorEq`.

The variables:
- `H`: the bundle; `b₀`: the base slot; `s₁`: the slot.

Restated with the delivery premises up to `supportCutoff S s'`: through the bundle `FrontHypsUpTo`; the proof reads none of them. -/
theorem front_step_frames_upTo {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (b₀ : ℕ)
    (hb₀ : b₀ + 2 = s_w + 2 * S.C.k) (s₁ : ℕ) (h1 : b₀ ≤ s₁) (h2 : s₁ < s') :
    ∀ C : Block V, (liveLockAncestors S Sched x (Hon s₁) s₁ C ∨ ∃ v ∈ Hon (s₁ + 1),
        (stateBefore x (supportCutoff S (s₁ + 1) + 1) v).A.saved_confirmation s₁ = some C) →
      ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C s₁ w := by
  have hk := S.C.k_ge_two
  intro C hC w hw
  rcases hC with ⟨u, hu, e, he, hl, hCe⟩ | ⟨v, hv, hC⟩
  · have hl' := hl
    simp only [is_live_iff] at hl'
    obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := lock_entry_confirmation S Sched x _ u e H.hDiv he
    have hσlo : s_w + S.C.k - 1 ≤ σ :=
      GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S (s_w + S.C.k - 1) σ
        (voteTime S (s₁ + 1)) e hd hl'.1 (voteTime_mono S (by omega))
    have hσhi : σ + 1 ≤ s₁ := by
      by_contra h
      have hm := slotStart_mono S (show s₁ + 1 ≤ σ + 1 by omega)
      have h1' := voteTime_eq S (s₁ + 1)
      have h2' := supportCutoff_eq S (σ + 1)
      have h3' := voteTime_eq S (σ + 1)
      omega
    have hu' : u ∈ Hon (σ + 1) := H.anti (σ + 1) s₁ (by omega) hσhi (by omega) hu
    exact stepFrameAt_of_ancestorEq S Sched x C' C s₁ w (ancestorEq_trans hCe heC')
      (H.hFrame s₁ (by omega) h2 σ hσlo (by omega) u hu' C' hsv w hw)
  · exact H.hFrame s₁ (by omega) h2 s₁ (by omega) le_rfl v hv C hC w hw

/-- **The chain relative to the live lock blocks, from slot `b₀`.** Under the bundle, with
`b₀ + 2 = s_w + 2k`: at every slot `b₀ + d < s'`, `ChainInvFor` holds at `Hon (b₀ + d)` for the
blocks on the chain of a live lock a member of that set holds before the vote time of the next
slot.

Why: at `b₀`, `front_lock_base` for each lock and `honestChainExtends_of_ancestorEq`; from `b₀ + d`
to `b₀ + d + 1`, the phase step `lem89s_phase_step` with the family of slot `b₀ + d`, its lock
invariant from Lemma 38 (`liveLocksOnFamilyAt_of_live`), its frames from `front_step_frames`, and
the family of the next slot inside the step's (`liveLockAncestors_succ`).

The variables:
- `H`: the bundle; `b₀`: the base slot.

Restated with the delivery premises up to `supportCutoff S s'`: through the bundle `FrontHypsUpTo`; the base and the phase step at the slots before `s'` read deliveries due by the support cutoff of slot `s'`. -/
theorem front_locks_chain_upTo {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHypsUpTo S Sched x GST tGAT tAwakeEnd s_w s' Hon) (b₀ : ℕ)
    (hb₀ : b₀ + 2 = s_w + 2 * S.C.k) :
    ∀ d, b₀ + d < s' → ChainInvFor S Sched x (Hon (b₀ + d))
      (liveLockAncestors S Sched x (Hon (b₀ + d)) (b₀ + d)) (b₀ + d) := by
  have hk := S.C.k_ge_two
  intro d
  induction d with
  | zero =>
      intro hd C hC
      obtain ⟨u, hu, e, he, hl, hCe⟩ := hC
      exact honestChainExtends_of_ancestorEq S Sched x _ e.B C _ hCe
        (front_lock_base_upTo H b₀ hb₀ (by omega) u hu e he hl)
  | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      rw [show b₀ + (d + 1) = b₀ + d + 1 by omega]
      have hstep := (lem89s_phase_step_upTo S Sched x GST (b₀ + d) (Hon (b₀ + d)) (Hon (b₀ + d + 1))
        (liveLockAncestors S Sched x (Hon (b₀ + d)) (b₀ + d)) H.hDiv H.hMono
        (H.hSync.mono (supportCutoff_mono S (by omega)))
        (H.hCatch.mono (supportCutoff_mono S (by omega)))
        (H.rootsAt (supportCutoff_mono S (by omega))) H.hParent H.hOwner
        (H.gst _ (by omega)) (H.window (b₀ + d) (by omega) (by omega))
        (H.window (b₀ + d + 1) (by omega) (by omega))
        (H.hHonMono (b₀ + d) (by omega) (by omega))
        (H.hCommittees (b₀ + d) (by omega) (by omega))
        (H.hCommittees (b₀ + d + 1) (by omega) (by omega)) ih'
        (fun u hu => liveLocksOnFamilyAt_of_live S Sched x _ (b₀ + d) u
          (fun e he hl => ⟨u, hu, e, he, hl, ancestorEq_refl e.B⟩))
        (front_step_frames_upTo H b₀ hb₀ (b₀ + d) (by omega) (by omega))).1
      intro C hC
      exact hstep C (liveLockAncestors_succ_upTo H (b₀ + d) (by omega) (by omega) C hC)

/-- **Lemma 89f with the frame hypotheses its proof reads.** The proof; the audited statement is
in `Statements/Executions/Lemma89fStatements.lean`.

Why: with `b₀ := s_w + 2k − 2` and `s' = m + 1`: `front_locks_chain` at slot `m`, the phase step
`lem89s_phase_step` from `m` to `m + 1`, whose family holds every block of
`FrontFamily S Sched x (Hon s') s'`: a live lock block by `liveLockAncestors_succ`, a root by
`hRootsOn` and the same. The lock invariant relative to `FrontFamily` is Lemma 38
(`liveLocksOnFamilyAt_of_live`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `s_w`: a slot whose duty window starts
  at or after `tGAT`; `s'`: the slot; `Hon`: the member sets.

Roots name blocks until `supportCutoff S s'`: the base reads Lemmas 45b, 12 and 78 at the slot
`σ + 1 ≤ s'` after a lock's slot (`front_lock_base`), the carry and the phase step at slots before
`s'`, up to the support cutoff of slot `s'`.

Restated with the delivery premises up to `supportCutoff S s'`: the base, the carry and the phase step read deliveries due by the support cutoff of slot `s'` (`front_locks_chain_upTo`, `lem89s_phase_step_upTo`). -/
theorem lem89fq_front_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s'))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s'))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ tGAT)
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : ∀ s₁, s_w + S.C.k ≤ s₁ → s₁ ≤ s' →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    (hsw : tGAT ≤ dutyWindowStart S s_w)
    (hs' : s_w + 2 * S.C.k - 1 ≤ s') (hEnd : supportCutoff S (s' + 1) ≤ tAwakeEnd)
    (hFrame : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
      ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
        ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C s₁ w)
    (hRootsOn : ∀ w ∈ Hon s', ∃ D : Block V,
      ((∃ u ∈ Hon s', ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
          is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
            ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
        ∃ v ∈ Hon s',
          (stateBefore x (supportCutoff S s' + 1) v).A.saved_confirmation (s' - 1) = some D) ∧
      (get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S).AncestorEq D) :
    ChainInvFor S Sched x (Hon s') (FrontFamily S Sched x (Hon s') s') s' ∧
    ∀ u ∈ Hon s', LiveLocksOnFamilyAt S Sched x (FrontFamily S Sched x (Hon s') s') s' u := by
  have hk := S.C.k_ge_two
  have H : FrontHypsUpTo S Sched x GST tGAT (supportCutoff S (s' + 1)) s_w s' Hon :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hOwner, hGST, hHonMono, hHon,
      fun t h1 h2 => hAwake t h1 (le_trans h2 hEnd), hCommittees, hsw, le_rfl, hFrame⟩
  refine ⟨?_, fun u hu => liveLocksOnFamilyAt_of_live S Sched x _ s' u
    (fun e he hl => Or.inl ⟨u, hu, e, he, hl, rfl⟩)⟩
  obtain ⟨m, rfl⟩ : ∃ m, s' = m + 1 := ⟨s' - 1, by omega⟩
  have hb₀ : (s_w + 2 * S.C.k - 2) + 2 = s_w + 2 * S.C.k := by omega
  have hm := front_locks_chain_upTo H (s_w + 2 * S.C.k - 2) hb₀ (m - (s_w + 2 * S.C.k - 2)) (by omega)
  rw [show s_w + 2 * S.C.k - 2 + (m - (s_w + 2 * S.C.k - 2)) = m by omega] at hm
  have hstep := (lem89s_phase_step_upTo S Sched x GST m (Hon m) (Hon (m + 1))
    (liveLockAncestors S Sched x (Hon m) m) hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner
    (H.gst _ (by omega)) (H.window m (by omega) (by omega)) (H.window (m + 1) (by omega) le_rfl)
    (hHonMono m (by omega) (by omega)) (hCommittees m (by omega) (by omega))
    (hCommittees (m + 1) (by omega) le_rfl) hm
    (fun u hu => liveLocksOnFamilyAt_of_live S Sched x _ m u
      (fun e he hl => ⟨u, hu, e, he, hl, ancestorEq_refl e.B⟩))
    (front_step_frames_upTo H (s_w + 2 * S.C.k - 2) hb₀ m (by omega) (by omega))).1
  intro C hC
  apply hstep C
  rcases hC with ⟨w, hw, e, he, hl, rfl⟩ | ⟨w, hw, rfl⟩
  · exact liveLockAncestors_succ_upTo H m (by omega) le_rfl e.B ⟨w, hw, e, he, hl, ancestorEq_refl e.B⟩
  · obtain ⟨D, hD, hRD⟩ := hRootsOn w hw
    rcases hD with ⟨u, hu, e, he, hl, rfl⟩ | ⟨v, hv, hconf⟩
    · exact liveLockAncestors_succ_upTo H m (by omega) le_rfl _ ⟨u, hu, e, he, hl, hRD⟩
    · rw [Nat.add_sub_cancel] at hconf
      exact Or.inr ⟨v, hv, D, hconf, hRD⟩

end GoldilocksCorrectness.Proofs.Executions

