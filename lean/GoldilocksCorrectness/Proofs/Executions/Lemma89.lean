module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Statements.Executions.Lemma89fStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Lemma36a
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# Lemma 89: the events of the phase and the counting kit

The proofs of the statements of `GoldilocksCorrectness/Statements/Executions/Lemma89Statements.lean`
and their kit:

- the span premise: a span of `L` slots holds at most `⌈L / R⌉` openings, the plain count implies
  the span premises of two and three span lengths, and with ceilings
  `OpeningsOutsideWaitsAndWindows`;
- where a waiting opening and an opening whose window an object's arrivals break lie;
- the committee premise's anchor against the phase's slots;
- the hypotheses of the re-base, the front and Lemma 89r from the phase's member sets;
- `quietRound_cases`, the negation of `QuietRoundOnConfirmations` written out;
- the classification facts: the justified block and the finalized block are at a height at most
  `h₀ + 1` or are entries of the honest chain at a slot whose update ran, and a
  `head_height_floor` past a height is a held block reaching past it, through a certificate at a
  height at most `h₀ + 1` or through the honest chain's entry at that height;
- `floor_of_root_ne_J`: a root that is not the justified block puts `head_height_floor` past the
  cache `h_j`;
- `frontWindowStable_fail_event`, the failure of `FrontWindowStable` written out, with its kit:
  a saved confirmation was held by its saver before the support cutoff of its slot, and a failed
  `StepFrameAt` relative to a confirmation, written out.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono supportCutoff_cast
  supportCutoff_eq supportCutoff_mono voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_genesis_h)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq floor_le_h_max mem_fg_to_ac_tree
  mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes mem_viable_tree_iff
  pool_of_keepsVotes tau_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn
  RootsNameBlocksIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The span premise -/

omit [RootOrder] in
/-- A sequence of rounds increasing up to `m` increases between any two indices up to `m`. -/
theorem r_lt_of_lt_of_mono (r : ℕ → ℕ) (m : ℕ) (hMono : ∀ i : ℕ, i < m → r i < r (i + 1)) :
    ∀ i j : ℕ, i < j → j ≤ m → r i < r j := by
  intro i j hij hjm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact lt_trans (ih h (by omega)) (hMono j (by omega))
    · subst h; exact hMono i (by omega)

omit [RootOrder] in
/-- **A span of `L` slots holds at most `⌈L / R⌉` openings.** When the rounds `r 0 < … < r m`
increase, at most `(L + R − 1) / R` indices `i ≤ m` have `r i * R` in the span `[a, a + L)`.

Why: `i ↦ r i − ⌈a / R⌉` is injective and lands in `{0, …, ⌈L / R⌉ − 1}`.

The variables:
- `r`: the rounds; `m`: the last index; `R`: the slots per round; `a`, `L`: the span. -/
theorem card_filter_inSpan_le (r : ℕ → ℕ) (m R a L : ℕ) (hR : 1 ≤ R)
    (hMono : ∀ i : ℕ, i < m → r i < r (i + 1)) :
    ((Finset.range (m + 1)).filter (fun i => InSpan a L (r i * R))).card ≤ (L + R - 1) / R := by
  set c := (a + R - 1) / R with hc
  have hcR : a ≤ c * R := by
    have h1 : c * R + (a + R - 1) % R = a + R - 1 := by
      rw [hc, Nat.mul_comm]; exact Nat.div_add_mod _ _
    have h2 := Nat.mod_lt (a + R - 1) (by omega : 0 < R)
    omega
  have hc_le : ∀ i ∈ (Finset.range (m + 1)).filter (fun i => InSpan a L (r i * R)), c ≤ r i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have h1 : a ≤ r i * R := hi.2.1
    rw [hc, Nat.div_le_iff_le_mul_add_pred (by omega : 0 < R), Nat.mul_comm]
    omega
  have key : ∀ i ∈ (Finset.range (m + 1)).filter (fun i => InSpan a L (r i * R)),
      r i - c ∈ Finset.range ((L + R - 1) / R) := by
    intro i hi
    have hci := hc_le i hi
    rw [Finset.mem_filter] at hi
    have h2 : r i * R < a + L := hi.2.2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, r i = c + n := ⟨r i - c, by omega⟩
    have hmul : (c + n) * R = c * R + n * R := Nat.add_mul c n R
    have hnR : n * R < L := by rw [hn, hmul] at h2; omega
    have hn' : n + 1 ≤ (L + R - 1) / R := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < R), Nat.add_mul, Nat.one_mul]
      omega
    rw [Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun i => r i - c)
      (((Finset.range (m + 1)).filter (fun i => InSpan a L (r i * R)) : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    have hci := hc_le i hi
    have hcj := hc_le j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi hj
    have hrij : r i = r j := by simp only at hij; omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd hrij (ne_of_lt (r_lt_of_lt_of_mono r m hMono i j h (by omega)))
    · exact absurd hrij (ne_of_gt (r_lt_of_lt_of_mono r m hMono j i h (by omega)))
  calc ((Finset.range (m + 1)).filter (fun i => InSpan a L (r i * R))).card
      ≤ (Finset.range ((L + R - 1) / R)).card :=
        Finset.card_le_card_of_injOn (fun i => r i - c) (fun i hi => key i hi) hinj
    _ = (L + R - 1) / R := Finset.card_range _

omit [RootOrder] in
/-- **The plain count implies the span premise.** When the rounds increase and
`need + nWait · ⌈Lwait / R⌉ + nWin · ⌈Lwin / R⌉ ≤ m + 1`, at least `need` of the `m + 1` openings
fall outside every choice of `nWait` spans of `Lwait` slots and `nWin` spans of `Lwin` slots.

Why: each span holds at most `⌈L / R⌉` openings (`card_filter_inSpan_le`).

The variables:
- `S`: the setup; `r`: the rounds; `m`: the last index;
- `nWait`, `Lwait`, `nWin`, `Lwin`: the numbers and the lengths of the spans; `need`: the bound. -/
theorem plainCount_implies_spans (S : Setup V) (r : ℕ → ℕ) (m nWait Lwait nWin Lwin need : ℕ)
    (hMono : ∀ i : ℕ, i < m → r i < r (i + 1))
    (hm : need + nWait * ((Lwait + S.C.R - 1) / S.C.R) + nWin * ((Lwin + S.C.R - 1) / S.C.R)
      ≤ m + 1) :
    OpeningsOutsideSpans S r m nWait Lwait nWin Lwin need := by
  intro waits wins
  have hR : 1 ≤ S.C.R := by have := S.C.R_ge_two; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (m + 1))
    (OutsideSpans S r waits Lwait wins Lwin)
  rw [Finset.card_range] at hsplit
  have hsub : (Finset.range (m + 1)).filter (fun i => ¬ OutsideSpans S r waits Lwait wins Lwin i) ⊆
      (Finset.univ.biUnion fun j : Fin nWait =>
        (Finset.range (m + 1)).filter (fun i => InSpan (waits j) Lwait (r i * S.C.R))) ∪
      (Finset.univ.biUnion fun j : Fin nWin =>
        (Finset.range (m + 1)).filter (fun i => InSpan (wins j) Lwin (r i * S.C.R))) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hi, hnP⟩ := hi
    rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
    simp only [OutsideSpans, not_and_or, not_forall, not_not] at hnP
    rcases hnP with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨j, Finset.mem_univ j, Finset.mem_filter.2 ⟨hi, hj⟩⟩
    · exact Or.inr ⟨j, Finset.mem_univ j, Finset.mem_filter.2 ⟨hi, hj⟩⟩
  have hb1 : (Finset.univ.biUnion fun j : Fin nWait =>
      (Finset.range (m + 1)).filter (fun i => InSpan (waits j) Lwait (r i * S.C.R))).card ≤
      nWait * ((Lwait + S.C.R - 1) / S.C.R) := by
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ ((Lwait + S.C.R - 1) / S.C.R)
      fun j _ => card_filter_inSpan_le r m S.C.R (waits j) Lwait hR hMono) ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have hb2 : (Finset.univ.biUnion fun j : Fin nWin =>
      (Finset.range (m + 1)).filter (fun i => InSpan (wins j) Lwin (r i * S.C.R))).card ≤
      nWin * ((Lwin + S.C.R - 1) / S.C.R) := by
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ ((Lwin + S.C.R - 1) / S.C.R)
      fun j _ => card_filter_inSpan_le r m S.C.R (wins j) Lwin hR hMono) ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    (Finset.univ.biUnion fun j : Fin nWait =>
      (Finset.range (m + 1)).filter (fun i => InSpan (waits j) Lwait (r i * S.C.R)))
    (Finset.univ.biUnion fun j : Fin nWin =>
      (Finset.range (m + 1)).filter (fun i => InSpan (wins j) Lwin (r i * S.C.R)))
  omega

omit [RootOrder] in
/-- **The plain count with ceilings implies the span premise of the phase.** When the rounds
`r 0 < … < r m` increase and `9 + 2 ⌈δt / R⌉ + 5 ⌈(k + 2) / R⌉ ≤ m`, then for every choice
of two spans of `δt` slots and five spans of `k + 2` slots, at least 9 of the honest round opening
slots fall outside all of them (`OpeningsOutsideWaitsAndWindows`). In `ℕ`, `⌈x / R⌉` is written
`(x + R − 1) / R`. The proof is `plainCount_implies_spans` with two spans of `δt` slots, five of
`k + 2` slots and nine honest round opening slots.

The variables:
- `S`: the setup; `r`: the rounds; `m`: the last index.

Read aloud: if the rounds `r 0, …, r m` increase and `m` is at least
`9 + 2 ⌈δt / R⌉ + 5 ⌈(k + 2) / R⌉`, then however two spans of `δt` slots and five of `k + 2` slots
are placed, at least nine of the honest round opening slots fall outside all seven. -/
theorem plainCountCeil_implies_waitsAndWindows (S : Setup V) (r : ℕ → ℕ) (m : ℕ)
    (hMono : ∀ i : ℕ, i < m → r i < r (i + 1))
    (hm : 9 + 2 * ((S.C.δt + S.C.R - 1) / S.C.R) + 5 * ((S.C.k + 2 + S.C.R - 1) / S.C.R) ≤ m) :
    OpeningsOutsideWaitsAndWindows S r m :=
  plainCount_implies_spans S r m 2 S.C.δt 5 (S.C.k + 2) 9 hMono (by omega)

/-! ## Where the spans go -/

omit [RootOrder] in
/-- **A waiting opening lies in the wait span of its height.** With `s` the slot of the entry of
the height, `s₀ ≤ s₁` the first slots of the first round at the height and of a waiting round
there, and `s₂` the first slot of the opening after the waiting round: when `s ≤ s₀`,
`s₁ + R ≤ s₂` and `s₂ < s + δt`, the slot `s₁` is in `[s, s + δt)` and in `[s, s + δt − R)`.

The variables:
- `R`, `δt`: the slots per round and the timeout; `s`, `s₀`, `s₁`, `s₂`: the slots. -/
theorem waiting_opening_in_wait_span (R δt s s₀ s₁ s₂ : ℕ) (hs : s ≤ s₀) (h₀ : s₀ ≤ s₁)
    (h₁ : s₁ + R ≤ s₂) (h₂ : s₂ < s + δt) :
    InSpan s δt s₁ ∧ InSpan s (δt - R) s₁ := by
  unfold InSpan
  omega

omit [RootOrder] in
/-- **An opening whose window an object's arrivals break lies in the span of `k + 2` slots from
the slot of the first arrival.** With `σ` the slot of the object's first arrival at time `t`, and
an arrival at some member at a time `t'` from `t` to `t + Δ`: when `t'` is at or after the vote time
of slot `s − k − 1` and before the vote time of slot `s` (`k + 1 ≤ s`), the slot `s` is in
`[σ, σ + k + 2)`. The window reads `k + 1` slots, and the arrivals' spread over one delay adds one.

The variables:
- `S`: the setup; `s`: the honest round opening slot; `σ`: the slot of the first arrival;
- `t`, `t'`: the first arrival and the member's arrival. -/
theorem broken_window_in_window_span (S : Setup V) (s σ t t' : ℕ) (hk : S.C.k + 1 ≤ s)
    (hσ : slotStart S σ ≤ t) (hσ' : t < slotStart S (σ + 1))
    (ht : t ≤ t') (ht' : t' ≤ t + Δ S)
    (hw₁ : voteTime S (s - S.C.k - 1) ≤ t') (hw₂ : t' < voteTime S s) :
    InSpan σ (S.C.k + 2) s := by
  have hΔ := one_le_Δ S
  have e₂ := voteTime_eq S (s - S.C.k - 1)
  have e₃ := voteTime_eq S s
  rw [slotStart_eq] at e₂ e₃ hσ hσ'
  have h₁ : 4 * Δ S * (s - S.C.k - 1) < 4 * Δ S * (σ + 1) := by omega
  have h₁' := Nat.lt_of_mul_lt_mul_left h₁
  have h₅ : 4 * Δ S * σ < 4 * Δ S * (s + 1) := by
    rw [Nat.mul_add_one (4 * Δ S) s]
    omega
  have h₂ := Nat.lt_of_mul_lt_mul_left h₅
  unfold InSpan
  exact ⟨by omega, by omega⟩

/-! ## The committee premise's anchor -/

/-! ## The hypotheses of the round lemmas from the phase's member sets -/

omit [RootOrder] in
/-- **The re-base's members are awake and honest through the update of slot `s`.** Under
permanent corruption, with every validator honest at a time of the phase awake then, the duty
window of slot `s` starting at or after `tGAT` and the support cutoff of slot `s + 1` inside the
phase: every member of `roundMembers S Sched (s + 1)` is awake and honest at every time from the
duty window's start of slot `s` to the support cutoff of slot `s + 1`.

The variables:
- `S`, `Sched`: the setup, the schedule; `tGAT`, `tAwakeEnd`: the ends of the phase; `s`: the
  slot. -/
theorem rebase_window_of_roundMembers (S : Setup V) (Sched : Schedule V) (tGAT tAwakeEnd s : ℕ)
    (hMono : Sched.MonotoneCorruption)
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hsw : tGAT ≤ dutyWindowStart S s)
    (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    ∀ v ∈ roundMembers S Sched (s + 1), ∀ t : ℕ,
      dutyWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := by
  intro v hv t h1 h2
  simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
  have hadv : v ∉ Sched.adv (t : Int) := fun ha => hv (hMono _ _ (by exact_mod_cast h2) ha)
  exact ⟨hAwake t (by omega) (by omega) v hadv, hadv⟩

/-- **The base at an opening's slot `s`, from a stable window.** `lem89fq_front` with
`s_w := s − 2k` and `s' := s − 1`: when the frames of the members are stable through the `2k − 1`
slots before `s`, the chain invariant and the lock invariant hold at slot `s − 1` for the family
of the members' live lock blocks and roots.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times of the phase; `s`: the honest round opening slot; `Hon`: one member set per slot.

Roots name blocks until `supportCutoff S (s - 1)`: `lem89fq_front` at `s' := s − 1`. -/
theorem front_of_frontWindowStable (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s : ℕ) (Hon : ℕ → Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ tGAT)
    (hk : 2 * S.C.k ≤ s)
    (hHonMono : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ < s - 1 → Hon (s₁ + 1) ⊆ Hon s₁)
    (hHon : ∀ s₁, s - 2 * S.C.k ≤ s₁ → s₁ ≤ s - 1 → ∀ v ∈ Hon s₁,
      v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : ∀ s₁, s - 2 * S.C.k + S.C.k ≤ s₁ → s₁ ≤ s - 1 →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    (hsw : tGAT ≤ dutyWindowStart S (s - 2 * S.C.k))
    (hEnd : supportCutoff S (s - 1 + 1) ≤ tAwakeEnd)
    (hStable : FrontWindowStable S Sched x Hon (s - 2 * S.C.k) (s - 1)) :
    ChainInvFor S Sched x (Hon (s - 1)) (FrontFamily S Sched x (Hon (s - 1)) (s - 1)) (s - 1) ∧
    ∀ u ∈ Hon (s - 1),
      LiveLocksOnFamilyAt S Sched x (FrontFamily S Sched x (Hon (s - 1)) (s - 1)) (s - 1) u :=
  GoldilocksCorrectness.Statements.Executions.lem89fq_front S Sched x GST tGAT tAwakeEnd
    (s - 2 * S.C.k) (s - 1) Hon hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    hHonMono hHon hAwake hCommittees hsw (by omega) hEnd hStable.1 hStable.2

/-- **The proposer clause relative to `C` gives a viable head on `C`'s chain.** When, before `t`,
`p`'s fork-choice root is compatible with `C` and, if it is `C` or an ancestor of `C`, some viable
head of `p`'s frame is `C` or a descendant of `C`, then some viable head of `p`'s frame is `C` or a
descendant of `C`.

Why: when the root is not `C` or an ancestor of `C`, compatibility makes `C` an ancestor of the
root, and every viable head descends from the root.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator;
  `C`: the block. -/
theorem frameP_of_proposerClause (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (p : V) (C : Block V)
    (hClause : (fg_to_ac (stateBefore x t p).S).fc_root.compatible C = true ∧
      ((fg_to_ac (stateBefore x t p).S).fc_root.AncestorEq C →
        ∃ W ∈ (fg_to_ac (stateBefore x t p).S).tree,
          W ∈ (fg_to_ac (stateBefore x t p).S).viable_heads ∧ C.AncestorEq W)) :
    ∃ W ∈ (fg_to_ac (stateBefore x t p).S).tree,
      W ∈ (fg_to_ac (stateBefore x t p).S).viable_heads ∧ C.AncestorEq W := by
  by_cases hroot : (fg_to_ac (stateBefore x t p).S).fc_root.AncestorEq C
  · exact hClause.2 hroot
  · have hCρ : C.AncestorEq (fg_to_ac (stateBefore x t p).S).fc_root :=
      ((compatible_iff _ _).1 hClause.1).resolve_left hroot
    obtain ⟨W, hW⟩ := GoldilocksCorrectness.Statements.Executions.frame_has_viable_head S Sched x
      t p
    have hW' := (mem_viable_heads_iff _ _).1 hW
    exact ⟨W, (mem_fg_to_ac_tree _ _).2 ⟨hW'.1, hW'.2.1⟩, hW,
      ancestorEq_trans hCρ hW'.2.2.1⟩

/-- **A viable head on the chain of an ancestor of the proposal's parent.** When `B.parent` is in
the viable tree of `p`'s frame before `t` and `C` is `B.parent` or an ancestor of it, some viable
head of `p`'s frame is `C` or a descendant of `C`.

Why: a block of the viable tree has a viable head among its descendants.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator;
  `B`: the proposal; `C`: the block. -/
theorem frameP_of_viableTree_parent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (p : V) (B C : Block V)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x t p).S)
      (fg_to_ac (stateBefore x t p).S).tree)
    (hC : C.AncestorEq B.parent) :
    ∃ W ∈ (fg_to_ac (stateBefore x t p).S).tree,
      W ∈ (fg_to_ac (stateBefore x t p).S).viable_heads ∧ C.AncestorEq W := by
  simp only [mem_viable_tree_iff, Finset.mem_inter] at hParentIn
  obtain ⟨_, _, W, ⟨hWtree, hWvh⟩, hBW⟩ := hParentIn
  exact ⟨W, hWtree, hWvh, ancestorEq_trans hC hBW⟩

/-- **A failed proposer clause at a holder of the block is an event.** When the proposer clause
relative to `B` fails at `w` before `t` and `w` holds `B` then, `w`'s root before `t` is not `B` or
an ancestor of `B`, or its `head_height_floor` is greater than `B`'s chain-state height.

Why: when the root is `B` or an ancestor of `B`, `B` is in the frame tree (the finalized block is
an ancestor of the root), and with the `head_height_floor` at most `B`'s height `B` would itself
be a viable head.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the validator;
  `B`: the block. -/
theorem proposerClause_fail_event (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (w : V) (B : Block V)
    (hBw : B ∈ (stateBefore x t w).S.T)
    (hFail : ¬ ((fg_to_ac (stateBefore x t w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x t w).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x t w).S).tree,
          W ∈ (fg_to_ac (stateBefore x t w).S).viable_heads ∧ B.AncestorEq W))) :
    RootOffChainAt S Sched x w t B ∨
      HeadHeightFloorPastAt S Sched x w t (chainStateOf S.C B).h := by
  by_cases hroot : (fg_to_ac (stateBefore x t w).S).fc_root.AncestorEq B
  · right
    have hF : (stateBefore x t w).S.F.AncestorEq B :=
      ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x t w)
        (by rw [← fc_root_eq]; exact hroot)
    have hσ : (stateBefore x t w).S.σ B = chainStateOf S.C B :=
      (lem11_node_invariant S Sched x (stepBefore x t) w).1.2.2.2.2.2.1 B hBw
    unfold HeadHeightFloorPastAt
    by_contra hle
    push Not at hle
    apply hFail
    refine ⟨(compatible_iff _ _).2 (Or.inl hroot),
      fun _ => ⟨B, (mem_fg_to_ac_tree _ _).2 ⟨hBw, hF⟩, ?_, ancestorEq_refl B⟩⟩
    refine (mem_viable_heads_iff _ _).2 ⟨hBw, hF, hroot, ?_⟩
    rw [hσ]
    exact hle
  · left
    rw [fc_root_eq] at hroot
    exact hroot

/-- A bound on the honest attestations sent before `t` holds before every earlier time.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t'`, `t`: the two times; `H`: the
  bound. -/
theorem oldAttestationsAtMost_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t' t H : ℕ) (htt : t' ≤ t)
    (h : OldAttestationsAtMost S Sched x t H) : OldAttestationsAtMost S Sched x t' H :=
  fun i t₁ v a hl ht₁ hAw hHon hsent => h i t₁ v a hl (lt_of_lt_of_le ht₁ htt) hAw hHon hsent

/-! ## A round that is not quiet -/

/-- **A round that is not quiet relative to its own confirmations, written out.** When
`QuietRoundOnConfirmations S Sched x Hon B s s''` fails: some member of `Hon s` has its root off
`B.parent`'s chain or its `head_height_floor` past `h(B.parent)` before the vote time of slot `s`,
or its root off `B`'s chain or its `head_height_floor` past `h(B)` before the action time; or at a
slot `s'` of the round some member of `Hon (s' + 1)` fails `StepFrameAt` relative to `B`; or
relative to a confirmation a member of `Hon σ` saved for a slot `σ` from `s − 1` to `s'`; or the
proposer of slot `s''` has, before the start of slot `s''`, its root off the chain of every
confirmation of slot `s'' − 2` a member of `Hon (s'' − 2)` saved, or no viable head on that
confirmation's chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: one member set per slot;
- `B`: the round's proposal; `s`: its first slot; `s''`: the next honest round opening slot. -/
theorem quietRound_cases (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    (hNotQuiet : ¬ QuietRoundOnConfirmations S Sched x Hon B s s'') :
    (∃ w ∈ Hon s,
      RootOffChainAt S Sched x w (voteTime S s) B.parent ∨
      HeadHeightFloorPastAt S Sched x w (voteTime S s) (chainStateOf S.C B.parent).h ∨
      RootOffChainAt S Sched x w (supportCutoff S (s + 1)) B ∨
      HeadHeightFloorPastAt S Sched x w (supportCutoff S (s + 1)) (chainStateOf S.C B).h) ∨
    (∃ s', s ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt S Sched x B s' w) ∨
    (∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ σ, s - 1 ≤ σ ∧ σ ≤ s' ∧ ∃ v ∈ Hon σ,
      ∃ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C ∧
        ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt S Sched x C s' w) ∨
    (∀ C : Block V,
      (∃ v ∈ Hon (s'' - 2),
        (stateBefore x (supportCutoff S (s'' - 1) + 1) v).A.saved_confirmation (s'' - 2) =
          some C) →
      ¬ ((fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).fc_root.AncestorEq C ∧
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).viable_heads ∧
          C.AncestorEq W)) := by
  unfold QuietRoundOnConfirmations at hNotQuiet
  by_contra hNone
  apply hNotQuiet
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun s' hs hs' w hw => ?_,
    fun s' hs hs' σ hσ hσ' v hv C hC w hw => ?_, ?_⟩
  · by_contra hc
    apply hNone
    left
    refine ⟨w, hw, ?_⟩
    by_cases h1 : (get_fc_root (stateBefore x (voteTime S s) w).S).AncestorEq B.parent
    · right; left
      unfold HeadHeightFloorPastAt
      by_contra h2
      exact hc ⟨h1, Nat.le_of_not_lt h2⟩
    · left; exact h1
  · by_contra hc
    apply hNone
    left
    refine ⟨v, hv, ?_⟩
    by_cases h1 : (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B
    · right; right; right
      unfold HeadHeightFloorPastAt
      by_contra h2
      exact hc ⟨h1, Nat.le_of_not_lt h2⟩
    · right; right; left; exact h1
  · by_contra hc
    exact hNone (Or.inr (Or.inl ⟨s', hs, hs', w, hw, hc⟩))
  · by_contra hc
    exact hNone (Or.inr (Or.inr (Or.inl ⟨s', hs, hs', σ, hσ, hσ', v, hv, C, hC, w, hw, hc⟩)))
  · by_contra hc
    apply hNone
    refine Or.inr (Or.inr (Or.inr fun C hC hCl => hc ⟨C, hC, hCl⟩))

/-! ## The two classification facts -/

omit [DecidableEq V] [RootOrder] in
/-- Fewer than a quorum of validators in the adversary set up to `t` holds up to every earlier
time.

The variables:
- `Sched`: the schedule; `t'`, `t`: the two times. -/
theorem advQ_mono (Sched : Schedule V) {t' t : Int} (htt : t' ≤ t)
    (h : AdversaryFewerThanQuorumUntil Sched (quorum V) t) : AdversaryFewerThanQuorumUntil Sched (quorum V) t' :=
  fun A hA => h A fun v hv => by
    obtain ⟨t'', ht'', hv'⟩ := hA v hv
    exact ⟨t'', le_trans ht'' htt, hv'⟩

/-- **A held block certified at a height greater than `h₀ + 1` is an entry of the honest chain.**
Under unforgeability, roots naming blocks, permanent corruption and fewer than a quorum ever
corrupted up to `t`, with every honest attestation sent before the support cutoff of slot
`s₀ + 1` at a height at most `h₀ + 1`: when `w`, honest at `t`, holds before `t` a block `D` whose
chain carries a justification certificate at a height `h > h₀ + 1` for `T`, an ancestor of `D` or
`D` itself, then `T` is an entry block on the honest chain from `s₀` at a slot `s_a` whose update
ran by `t`.

Why: `cert_entry_at_slot` names an entry `E` with `T`'s root at such a slot, and the roots naming
blocks make it `T`, which `w` holds.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the holder; `D`: the held
  block; `T`: the certified block; `h`: the certificate's height.

Roots name blocks until `t`: the proof compares `T`, held by `w` at the step before `t`, with
the entry of the honest chain at a slot whose update ran by then. -/
theorem justified_entry_of_cert (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t h₀ : ℕ) (w : V) (D T : Block V) (h : Height)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (t : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ Sched.adv (t : Int))
    -- `w` holds `D` before `t`, and `T` is `D` or an ancestor of `D`
    (hD : D ∈ (stateBefore x t w).S.T) (hTD : T.AncestorEq D)
    -- `D`'s chain carries a justification certificate at `h` for `T`
    (hc : JustificationCertOn D h T)
    (hh : h₀ + 1 < h) :
    ∃ s_a : ℕ, supportCutoff S (s_a + 1) ≤ t ∧ OnHonestChainAt S Sched x s₀ s_a T ∧
      IsEntry S.C T := by
  set j := stepBefore x t with hjdef
  have hjt : x[j].time ≤ t := time_stepBefore_le x t
  have hwj : w ∉ Sched.adv (x[j].time : Int) := fun ha => hw (hMono _ _ (by exact_mod_cast hjt) ha)
  have hAdvQj : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int) :=
    advQ_mono Sched (by exact_mod_cast hjt) hAdvQ
  have hD' : D ∈ (x[j][w].st).S.T := hD
  obtain ⟨s_a, E, hsa, hEon, hEent, -, hroot⟩ := cert_entry_at_slot S Sched x s₀ (h₀ + 1) j w D T
    h hDiv hMono hU hAdvQj hOld hD' (progressCertOn_of_justificationCertOn hc) hh
  have hTT : T ∈ (x[j][w].st).S.T := ancestors_mem_T_of_exec S Sched x j w D T hD' hTD
  have hEq : T = E := hRoots _ _ ⟨j, w, hwj, hjt, hTT⟩
    (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a t E hEon (le_trans hsa hjt)) hroot
  subst hEq
  exact ⟨s_a, le_trans hsa hjt, hEon, hEent⟩

/-- **The justified block is old, or an entry of the honest chain confirmed by `t`.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a quorum ever corrupted
up to `t`, with every honest attestation sent before the support cutoff of slot `s₀ + 1` at a
height at most `h₀ + 1`: when `w` is honest at `t`, its justified block `J` before `t` has
chain-state height at most `h₀ + 1`, or `J` is an entry block on the honest chain from `s₀` at a
slot `s_a` whose update ran by `t` (`supportCutoff S (s_a + 1) ≤ t`).

Why: `J` and its height are those of the chain state of a held block (`CachesWitnessed`);
Lemma 66 gives the justification certificate at that height on that block's chain, and past
`h₀ + 1` `justified_entry_of_cert` names the slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the validator.

Read aloud: a justified block is either from before the first opening's action time or the
honest chain's own entry at its height, confirmed by then.

Roots name blocks until `t`: `justified_entry_of_cert` at `t`. -/
theorem justified_old_or_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t h₀ : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (t : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ Sched.adv (t : Int)) :
    (chainStateOf S.C (stateBefore x t w).S.J).h ≤ h₀ + 1 ∨
      ∃ s_a : ℕ, supportCutoff S (s_a + 1) ≤ t ∧
        OnHonestChainAt S Sched x s₀ s_a (stateBefore x t w).S.J ∧
        IsEntry S.C (stateBefore x t w).S.J := by
  obtain ⟨⟨D, hDT, hDJ, -⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  rw [hDJ]
  by_cases h0 : (chainStateOf S.C D).h_j = 0
  · left
    rw [(chainStateOf_J_spec S.C D).2.1 h0, chainStateOf_genesis_h]
    exact Nat.le_add_left 1 h₀
  · have h1 : 1 ≤ (chainStateOf S.C D).h_j := Nat.one_le_iff_ne_zero.mpr h0
    obtain ⟨hcert, hJD, hJh⟩ :=
      (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).1 h1
    by_cases hle : ((chainStateOf S.C D).h_j : ℕ) ≤ h₀ + 1
    · left
      rw [hJh]
      exact hle
    · right
      exact justified_entry_of_cert S Sched x s₀ t h₀ w D _ _ hDiv hMono hU hRoots hAdvQ hOld hw
        hDT hJD hcert (Nat.lt_of_not_le hle)

/-- **The finalized block is witnessed by a held block.** At every time, `w`'s finalized block
before `t` is the genesis block, or `w` holds a block `D` whose chain state finalized it, at a
finalization height at least `1`.

Why: the finalized block is the finalized block of the chain state of a held block
(`finalizedFromChain_of_exec`), and a chain state with finalization height `0` finalized the
genesis block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the
  validator. -/
theorem finalized_witnessed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (w : V) :
    (stateBefore x t w).S.F = Block.genesis ∨
      ∃ D ∈ (stateBefore x t w).S.T, (chainStateOf S.C D).F = (stateBefore x t w).S.F ∧
        1 ≤ (chainStateOf S.C D).h_F := by
  obtain ⟨B, hB, hF⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x t) w
  have hSt : stateBefore x t w = x[stepBefore x t][w].st := rfl
  rw [hSt]
  by_cases h0 : (chainStateOf S.C B).h_F = 0
  · left
    rw [hF]
    exact GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C B h0
  · exact Or.inr ⟨B, hB, hF.symm, Nat.one_le_iff_ne_zero.mpr h0⟩

/-- **The finalized block is old, or an entry of the honest chain confirmed by `t`.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a quorum ever corrupted
up to `t`, with every honest attestation sent before the support cutoff of slot `s₀ + 1` at a
height at most `h₀ + 1`: when `w` is honest at `t`, its finalized block before `t` has
chain-state height at most `h₀ + 1`, or it is an entry block on the honest chain from `s₀` at a
slot `s_a` whose update ran by `t`.

Why: `finalized_witnessed` gives the held block `D` that finalized it; Lemma 66's third conjunct
gives a justification certificate at the finalization height for it on `D`'s chain; then as
`justified_old_or_entry`. The genesis block has height `1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the validator.

Read aloud: a finalized block is from before the first opening's action time or the honest
chain's own entry at its height.

Roots name blocks until `t`: `justified_entry_of_cert` at `t`. -/
theorem finalized_old_or_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t h₀ : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (t : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ Sched.adv (t : Int)) :
    (chainStateOf S.C (stateBefore x t w).S.F).h ≤ h₀ + 1 ∨
      ∃ s_a : ℕ, supportCutoff S (s_a + 1) ≤ t ∧
        OnHonestChainAt S Sched x s₀ s_a (stateBefore x t w).S.F ∧
        IsEntry S.C (stateBefore x t w).S.F := by
  rcases finalized_witnessed S Sched x t w with hg | ⟨D, hDT, hDF, h1⟩
  · left
    rw [hg, chainStateOf_genesis_h]
    exact Nat.le_add_left 1 h₀
  · rw [← hDF]
    obtain ⟨hcert, -, hFD, hFh⟩ :=
      (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2 h1
    by_cases hle : ((chainStateOf S.C D).h_F : ℕ) ≤ h₀ + 1
    · left
      rw [hFh]
      exact hle
    · right
      exact justified_entry_of_cert S Sched x s₀ t h₀ w D _ _ hDiv hMono hU hRoots hAdvQ hOld hw
        hDT hFD hcert (Nat.lt_of_not_le hle)

/-- **A `head_height_floor` past a height is a held block reaching past it, through an old
certificate or through the honest chain's entry.** Under unforgeability, roots naming blocks,
permanent corruption and fewer than a quorum ever corrupted up to `t`, with every honest
attestation sent before the support cutoff of slot `s₀ + 1` at a height at most `h₀ + 1`: when
`w`, honest at `t`, has its `head_height_floor` before `t` greater than `h`, `w` holds a block `Z`
of chain-state height at least `h + 1`, and `h ≤ h₀ + 1`, or the entry `E` of `Z`'s chain at the
height `h` is an entry block on the honest chain from `s₀` at a slot `s_a` whose update ran by
`t`.

Why: `head_height_floor ≤ h_max`, the height of a held block; past a height `h ≥ h₀ + 2` that
block's chain carries a progress certificate at `h` (Lemma 67) naming the honest chain's entry
there at a slot whose update ran by `t` (`cert_entry_at_slot`, with the roots naming blocks).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first honest round opening slot;
  `t`: the time; `h₀`: the height of the proposal at the first honest round opening slot; `w`: the validator; `h`: the height.

Read aloud: past a height at least `h₀ + 2`, the block that raised `w`'s `h_max` passed that
height through the honest chain's own entry there.

Roots name blocks until `t`: the proof compares the entry `T_h` of a block's chain, held by `w`
at the step before `t`, with the entry of the honest chain at a slot whose update ran by then. -/
theorem headHeightFloorPast_old_or_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t h₀ : ℕ) (w : V) (h : Height)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (t : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (h₀ + 1))
    (hw : w ∉ Sched.adv (t : Int))
    (hEvent : HeadHeightFloorPastAt S Sched x w t h) :
    ∃ Z ∈ (stateBefore x t w).S.T, h + 1 ≤ (chainStateOf S.C Z).h ∧
      (h ≤ h₀ + 1 ∨
        ∃ (E : Block V) (s_a : ℕ), E.AncestorEq Z ∧ IsEntry S.C E ∧
          (chainStateOf S.C E).h = h ∧ supportCutoff S (s_a + 1) ≤ t ∧
          OnHonestChainAt S Sched x s₀ s_a E) := by
  unfold HeadHeightFloorPastAt at hEvent
  set j := stepBefore x t with hjdef
  have hjt : x[j].time ≤ t := time_stepBefore_le x t
  have hwj : w ∉ Sched.adv (x[j].time : Int) := fun ha => hw (hMono _ _ (by exact_mod_cast hjt) ha)
  have hAdvQj : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int) :=
    advQ_mono Sched (by exact_mod_cast hjt) hAdvQ
  have hSt : stateBefore x t w = x[j][w].st := rfl
  obtain ⟨-, ⟨Z, hZT, hZh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  have hfl : (head_height_floor (stateBefore x t w).S : ℕ) ≤ ((stateBefore x t w).S.h_max : ℕ) :=
    floor_le_h_max _
  have hZ : h + 1 ≤ (chainStateOf S.C Z).h := by
    rw [hZh]
    exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hEvent hfl)
  refine ⟨Z, hZT, hZ, ?_⟩
  by_cases hle : (h : ℕ) ≤ h₀ + 1
  · exact Or.inl hle
  · right
    have hle' : h₀ + 1 < (h : ℕ) := Nat.lt_of_not_le hle
    obtain ⟨Y, hYZ, -, hYp, -, hTY, hcert⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem67_first_advance S.C Z h
        (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left 1 h₀) hle')) (Nat.lt_of_succ_le hZ)
    rw [hSt] at hZT
    have hYT : Y ∈ (x[j][w].st).S.T := ancestors_mem_T_of_exec S Sched x j w Z Y hZT hYZ
    have hTT : (chainStateOf S.C Y.parent).T_h ∈ (x[j][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x j w Y _ hYT hTY
    obtain ⟨s_a, E, hsa, hEon, hEent, hEh, hroot⟩ := cert_entry_at_slot S Sched x s₀ (h₀ + 1) j w
      Y (chainStateOf S.C Y.parent).T_h h hDiv hMono hU hAdvQj hOld hYT hcert hle'
    have hEq : (chainStateOf S.C Y.parent).T_h = E := hRoots _ _ ⟨j, w, hwj, hjt, hTT⟩
      (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a t E hEon (le_trans hsa hjt)) hroot
    refine ⟨E, s_a, ?_, hEent, hEh, le_trans hsa hjt, hEon⟩
    rw [← hEq]
    exact ancestorEq_trans hTY hYZ

/-! ## A window that is not stable -/

/-- **A saved confirmation was held by its saver before the support cutoff of its slot.** When `v`
is awake and honest from the duty window's start of slot `s + 1` to the support cutoff of slot
`s + 1`, and its state right after that cutoff has `X` saved as the confirmation of slot `s`, then
`v` held `X` before the support cutoff of slot `s`.

Why: the update saved `X` because it passed the eligibility test, so `X` has an early supporter
at `v` (Lemma 36; the set of supporters is not empty, the voters being fewer than twice it), whose
vote resolved strictly before `S.C.t_ s + 2 · S.C.Δ`, the support cutoff of slot `s`; its head
block, `X` or a descendant of `X`, was then stamped before that cutoff (`tau_eq_some_blockStamp`),
so held before it (`blockStamp_lt_iff`), and so was `X`, an ancestor of it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of the confirmation;
  `v`: the saver; `X`: the confirmation.

Read aloud: a validator held its confirmation of slot `s` before the support cutoff of slot `s`. -/
theorem saved_confirmation_mem_T_supportCutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (v : V) (X : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s state right after that cutoff has `X` saved as the confirmation of slot `s`
    (hX : (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some X) :
    X ∈ (stateBefore x (supportCutoff S s) v).S.T := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hdwc : dutyWindowStart S (s + 1) < supportCutoff S (s + 1) := by omega
  have hvc := hv (supportCutoff S (s + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (supportCutoff S (s + 1)) v hDiv
    hMono hdwc (fun t h1 h2 => (hv t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x s v hDiv hvc hAw
  rw [hsave] at hX
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A'' _ _ (s + 1) X X hs1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hX) (ancestorEq_refl X)
  simp only [Nat.add_sub_cancel] at hSup hElig
  obtain ⟨u, hu⟩ : Sup.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨vote, -, -, ⟨H, hHΦ, hroot, hXH⟩, ⟨y, hy, hyb⟩, -⟩ := hSup u hu
  have hHΦ' : H ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree := hHΦ
  have hy' : (stateBefore x (supportCutoff S (s + 1)) v).A.tau
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) vote = .ok (some y) := by
    rw [tau_of_keepsVotes (expireLocks_keepsVotes _ _)] at hy; exact hy
  obtain ⟨y', hyy', hyc⟩ := (GoldilocksCorrectness.Proofs.Routines.occurrenceBefore_eq_true_iff _ _).1 hyb
  cases hyy'
  have hHT : H ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T := ((mem_fg_to_ac_tree _ _).1 hHΦ').1
  obtain ⟨τH, hτH, hτHy⟩ := GoldilocksCorrectness.Proofs.Routines.tau_eq_some_blockStamp hRootsΦv
    hHΦ' hroot hy'
  have hcast : ((((supportCutoff S s : ℕ) : Int)) : Stamp) =
      ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) := by
    rw [supportCutoff_cast]
  have hHc : H ∈ (stateBefore x (supportCutoff S s) v).S.T :=
    (blockStamp_lt_iff hDiv hHT).1 ⟨τH, hτH, by rw [hcast]; exact lt_of_le_of_lt hτHy hyc⟩
  exact ancestors_mem_T_of_exec S Sched x _ v H X hHc hXH


/-- **A failed chain step relative to a confirmation, written out.** Under synchrony from the
support cutoff of slot `σ`: when `v`, awake and honest through its update of slot `σ + 1`, saved
`X` as its confirmation of slot `σ ≤ s₁`, `w` is awake and honest for one delay from the support
cutoff of slot `σ`, and `StepFrameAt S Sched x X s₁ w` fails, then `w`'s root before the vote time
of slot `s₁ + 1` conflicts with `X`; or that root is `X` or an ancestor of `X`, `w` holds `X` then,
and no viable head of `w`'s voter tree of slot `s₁ + 1` is `X` or a descendant of `X`; or `w`'s
finalized block before the support cutoff of slot `s₁ + 2` conflicts with `X`.

Why: the three conjuncts of `StepFrameAt` negated; in the second case `v` held `X` before the
support cutoff of slot `σ` (`saved_confirmation_mem_T_supportCutoff`), and `w`, whose finalized
block is an ancestor of its root and so of `X`, received it within one delay
(`mem_T_before_add_delay_of_held`), before the vote time of slot `s₁ + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `σ ≤ s₁`: the slot of the confirmation and the slot of the step;
  `v`: the saver; `w`: the member; `X`: the confirmation.

Roots name blocks until `supportCutoff S σ + Δ S`: the proof takes `X`, which `v` holds before
the support cutoff of slot `σ`, as reaching `w` one delay later. -/
theorem stepFrameAt_fail_cases (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST σ s₁ : ℕ) (v w : V) (X : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S σ + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from the support cutoff of slot `σ` on
    (hGST : GST ≤ supportCutoff S σ)
    (hσ : σ ≤ s₁)
    -- `v` is awake and honest from the duty window's start of slot `σ + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (σ + 1) ≤ t → t ≤ supportCutoff S (σ + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w` is awake and honest for one delay from the support cutoff of slot `σ`
    (hw : ∀ t : ℕ, supportCutoff S σ ≤ t → t ≤ supportCutoff S σ + Δ S →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v`'s state right after the support cutoff of slot `σ + 1` has `X` saved for slot `σ`
    (hX : (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X)
    (hFail : ¬ StepFrameAt S Sched x X s₁ w) :
    RootIncompatibleAt S Sched x w (voteTime S (s₁ + 1)) X ∨
      ((get_fc_root (stateBefore x (voteTime S (s₁ + 1)) w).S).AncestorEq X ∧
        X ∈ (stateBefore x (voteTime S (s₁ + 1)) w).S.T ∧
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s₁ + 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S) (s₁ + 1) = .ok tree →
          ¬ ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S).viable_heads ∧
            X.AncestorEq W) ∨
      FinalizedIncompatibleAt S Sched x w (supportCutoff S (s₁ + 2)) X := by
  unfold StepFrameAt at hFail
  by_cases h1 : (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S).fc_root.compatible X = true
  · by_cases h3 : (stateBefore x (supportCutoff S (s₁ + 2)) w).S.F.compatible X = true
    · -- the second conjunct fails
      right; left
      have h2 : ¬ ((fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S).fc_root.AncestorEq X →
          ∀ tree : Finset (Block V),
            voter_block_tree S.C (stateBefore x (voteTime S (s₁ + 1)) w).A
              (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S) (s₁ + 1) = .ok tree →
            ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S).viable_heads ∧
              X.AncestorEq W) := fun h2 => hFail ⟨h1, h2, h3⟩
      push Not at h2
      obtain ⟨hroot, tree, htree, hno⟩ := h2
      have hroot' : (get_fc_root (stateBefore x (voteTime S (s₁ + 1)) w).S).AncestorEq X := by
        rw [← fc_root_eq]; exact hroot
      refine ⟨hroot', ?_, fun tree' htree' hex => ?_⟩
      · -- `w` holds `X`: the saver held it before the support cutoff of slot `σ`
        have hΔ := one_le_Δ S
        have hc₀ := supportCutoff_eq S σ
        have hv₀ := voteTime_eq S σ
        have hvs := voteTime_eq S (s₁ + 1)
        have hsm := slotStart_mono S (show σ + 1 ≤ s₁ + 1 by omega)
        have hss : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
          rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
        have hle : supportCutoff S σ + Δ S ≤ voteTime S (s₁ + 1) := by omega
        have hXv := saved_confirmation_mem_T_supportCutoff S Sched x σ v X hDiv hMono hv hX
        have hdw : dutyWindowStart S (σ + 1) ≤ slotStart S σ := dutyWindowStart_succ_le_slotStart S σ
        have hvh : v ∉ Sched.adv ((supportCutoff S σ : ℕ) : Int) :=
          (hv (supportCutoff S σ) (by omega) (by
            have := supportCutoff_eq S (σ + 1); have := voteTime_eq S (σ + 1); omega)).2
        have hFX : (stateBefore x (supportCutoff S σ + Δ S) w).S.F.compatible X = true := by
          refine (compatible_iff _ _).2 (Or.inl ?_)
          exact ancestorEq_trans (stateBefore_grows x hDiv w hle).2.1
            (ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hroot')
        have hXw := mem_T_before_add_delay_of_held hDiv hMono hSync hCatch hRoots hParent
          (t₁ := supportCutoff S σ) (t := supportCutoff S σ) (by omega) le_rfl hGST hvh hXv hw hFX
        exact (stateBefore_grows x hDiv w hle).1 hXw
      · rw [htree] at htree'
        cases htree'
        exact absurd hex (by
          push Not
          exact hno)
    · right; right
      exact h3
  · left
    rw [fc_root_eq] at h1
    exact h1


/-- **A failure of `FrontWindowStable`, written out.** Under the member sets shrinking from one slot
to the next and every member of the set of a slot honest at the support cutoff of the next slot:
when `FrontWindowStable S Sched x Hon s_w s'` fails, one of four things happens, each at a member
`w` of a set `Hon s₁` with `s_w + k − 1 ≤ s₁ ≤ s'`:

1. `w`, a member of `Hon (s₁ + 1)` with `s₁ < s'`, has its root before `voteTime S (s₁ + 1)` in
   conflict with a confirmation `X` a member saved for a slot from `s_w + k − 1` to `s₁`
   (`RootIncompatibleAt`);
2. or that root is `X` or an ancestor of such an `X`, `w` holds `X` then, and no block of `w`'s
   voter tree of slot `s₁ + 1` that is `X` or a descendant of `X` is a viable head;
3. or `w`'s finalized block before `supportCutoff S (s₁ + 2)` conflicts with such an `X`
   (`FinalizedIncompatibleAt`);
4. or, at `s₁ = s'`, `w`'s root before `voteTime S (s' + 1)` is `D` or an ancestor of `D` for no
   block `D` of a live lock entry of a member of `Hon s'` and no confirmation `D` of slot `s' − 1`
   of a member of `Hon s'` (`RootOffChainAt` at every such `D`).

Why: the two clauses of `FrontWindowStable` negated; the failure of the first is a failed
`StepFrameAt` (`stepFrameAt_fail_cases`), where `w` holds `X` in the second case by the delivery
of the saver's own copy.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase, in which every honest validator is
  awake; `s_w`: the slot the window is counted from; `s'`: its last slot; `Hon`: one member set
  per slot.

Read aloud: a window breaks at a member whose root or finalized block conflicts with a window
confirmation, whose frame finds no viable head on a confirmation's chain, or whose root is on no
family block's chain at the window's last slot.

Roots name blocks until `supportCutoff S (s' - 1) + Δ S`: `stepFrameAt_fail_cases` at a slot `σ`
at most `s' − 1`. -/
theorem frontWindowStable_fail_event (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' - 1) + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from `tGAT` on; the window has at least `2k − 1` slots
    (hGST : GST ≤ tGAT) (hs' : s_w + 2 * S.C.k - 1 ≤ s')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    -- every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int))
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    -- the duty window of slot `s_w` starts at or after `tGAT`; the support cutoff of slot
    -- `s' + 1` is inside the phase
    (hsw : tGAT ≤ dutyWindowStart S s_w) (hEnd : supportCutoff S (s' + 1) ≤ tAwakeEnd)
    -- the window is not stable
    (hFail : ¬ FrontWindowStable S Sched x Hon s_w s') :
    ∃ (s₁ : ℕ) (w : V), s_w + S.C.k - 1 ≤ s₁ ∧ s₁ ≤ s' ∧ w ∈ Hon s₁ ∧
      ((∃ X : Block V, WindowConfirmation S Sched x Hon (s_w + S.C.k - 1) s₁ X ∧ s₁ < s' ∧
          w ∈ Hon (s₁ + 1) ∧
          (RootIncompatibleAt S Sched x w (voteTime S (s₁ + 1)) X ∨
            ((get_fc_root (stateBefore x (voteTime S (s₁ + 1)) w).S).AncestorEq X ∧
              X ∈ (stateBefore x (voteTime S (s₁ + 1)) w).S.T ∧
              ∀ tree : Finset (Block V),
                voter_block_tree S.C (stateBefore x (voteTime S (s₁ + 1)) w).A
                  (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S) (s₁ + 1) = .ok tree →
                ¬ ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S).viable_heads ∧
                  X.AncestorEq W) ∨
            FinalizedIncompatibleAt S Sched x w (supportCutoff S (s₁ + 2)) X)) ∨
        (s₁ = s' ∧ ∀ D : Block V,
          ((∃ u ∈ Hon s', ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
              is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
                ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
            ∃ v ∈ Hon s',
              (stateBefore x (supportCutoff S s' + 1) v).A.saved_confirmation (s' - 1) = some D) →
          RootOffChainAt S Sched x w (voteTime S (s' + 1)) D)) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  unfold FrontWindowStable at hFail
  by_cases hc1 : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
      ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
        ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C s₁ w
  · -- clause 2 fails
    have hc2 : ¬ ∀ w ∈ Hon s', ∃ D : Block V,
        ((∃ u ∈ Hon s', ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
            is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
              ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
          ∃ v ∈ Hon s',
            (stateBefore x (supportCutoff S s' + 1) v).A.saved_confirmation (s' - 1) = some D) ∧
        (get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S).AncestorEq D :=
      fun h => hFail ⟨hc1, h⟩
    push Not at hc2
    obtain ⟨w, hw, hD⟩ := hc2
    exact ⟨s', w, by omega, le_rfl, hw, Or.inr ⟨rfl, fun D hDf => hD D hDf⟩⟩
  · -- clause 1 fails
    push Not at hc1
    obtain ⟨s₁, h1, h2, σ, hσ1, hσ2, v, hv, X, hX, w, hw, hst⟩ := hc1
    have hw₀ : w ∈ Hon s₁ := hHonMono s₁ (by omega) h2 hw
    have hvw := front_member_window S Sched tGAT tAwakeEnd s_w s' (σ + 1) Hon v hMono hHon hAwake
      hsw hEnd (by omega) (by omega) hv
    have hdm := dutyWindowStart_mono S (show s_w ≤ σ by omega)
    have hdc : dutyWindowStart S σ ≤ supportCutoff S σ :=
      dutyWindowStart_le_supportCutoff S (by omega)
    have hcs := supportCutoff_mono S (show s₁ + 2 ≤ s' + 1 by omega)
    have hc₀ := supportCutoff_eq S σ
    have hcσ := supportCutoff_mono S (show σ + 1 ≤ s₁ + 2 by omega)
    have hc₁ := supportCutoff_eq S (σ + 1)
    have hv₁ := voteTime_succ S σ
    have hwin : ∀ t : ℕ, supportCutoff S σ ≤ t → t ≤ supportCutoff S σ + Δ S →
        w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) := by
      intro t ht1 ht2
      have htc : t ≤ supportCutoff S (s₁ + 2) := by omega
      have hnot : w ∉ Sched.adv (t : Int) := fun h =>
        hHon (s₁ + 1) (by omega) (by omega) w hw (hMono _ _ (by exact_mod_cast htc) h)
      exact ⟨hAwake t (by omega) (by omega) w hnot, hnot⟩
    refine ⟨s₁, w, h1, by omega, hw₀, Or.inl ⟨X, ⟨σ, hσ1, hσ2, v, hv, hX⟩, h2, hw, ?_⟩⟩
    have hcR := supportCutoff_mono S (show σ ≤ s' - 1 by omega)
    exact stepFrameAt_fail_cases S Sched x GST σ s₁ v w X hDiv hMono hSync hCatch
      (hRoots.mono (by omega)) hParent (by omega) hσ2
      (fun t ht1 ht2 => hvw t ht1 (le_trans ht2 (supportCutoff_mono S (Nat.le_succ _))))
      hwin hX hst

end GoldilocksCorrectness.Proofs.Executions
