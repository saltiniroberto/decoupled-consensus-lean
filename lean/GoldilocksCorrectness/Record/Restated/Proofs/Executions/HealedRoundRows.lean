module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBaseSplit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedRoundRows, over a model

The rows `round_base_votes_upTo` and `round_base_updates_upTo` read, built from the hypotheses of C3
(`healed_round_base_of_prev_votes`) with clauses 1 and 3 of `RoundBaseAt` in place of the round base: every
validator outside the adversary set at the support cutoff of the round's first slot `s` holds the proposal `B` and
votes for it (`healed_round_votes_upTo`), and every updater of slot `s` whose finalized block is on `B`'s chain
saves `B`, makes it fast and keeps no lock off its chain (`healed_round_updates_upTo`). Each row is read at the
reader's own tick (rule R3). C3's helper `updater_saves_of_finalized_on_proposal` and C3's first conclusion call
them.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes FrameShape)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **At C3's round, every member holds the proposal and votes for it.** Under the hypotheses of C3
(`healed_round_base_of_prev_votes`), with clauses 1 and 3 of `RoundBaseAt` (`hBase1`, `hBase3`) in place of the
round base: every member `w` of `Hon M S A x s` (outside the adversary set after every step at a real time at
most the support cutoff of slot `s + 1`) holds `B` at its tick to the vote time of slot `s`, every slot-`s`
Goldfish vote `w`'s tick to that vote time puts on the wire is its vote for `B`'s root, and `B` is not genesis.

Why: `round_base_votes_upTo` with the members `Hon M S A x s`, the previous slot's voters the committee's members
of `Hon M S A x (s − 1)` with `X` the proposer's anchor (`hPrev`), the windows from `hAwake` (every validator
honest in the phase is awake), the values of `head_height_floor` ordered by delivery at both validators' ticks
(`floor_le_of_delivery_ticks`) and clause 1, the locks by clause 3, the slot's only block
(`only_block_of_unforgeability_st`) and the fresh root (`hNoCol`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- as C3's; `E`, `Sy`: the delivery facts up to the support cutoff of slot `s + 1`.

Read aloud: at a round whose base's first and third clauses hold, whose proposal's root is fresh and whose previous
slot's honest votes extend the proposer's anchor, every member holds the proposal and votes for it. -/
theorem healed_round_votes_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s + 1))
    (hA : anchorCW S tGAT ≤ M.slotStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hBase1 : ∀ w ∈ Hon M S A x s, (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h)
    (hBase3 : ∀ w ∈ Hon M S A x s, ∀ (n₁ : M.N) (sent₁ : List (NamedObject V)),
      .ok (n₁, sent₁) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n₁, M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e = true →
        e.B.AncestorEq B.parent)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon M S A x (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (M.get_anchor (x.tickInput (S.P.proposer s) (M.slotStart S.C s))
          ((M.slotStart S.C s : ℕ) : Int)).AncestorEq H_u) :
    (∀ u ∈ Hon M S A x s, B ∈ (x.tickInput u (M.voteTime S.C s)).tree) ∧
    (∀ u ∈ Hon M S A x s, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      vote = GoldfishVote.mk u s B.root) ∧
    B ≠ Block.genesis := by
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hPrev
  have hk := S.C.k_ge_two
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss1 : M.slotStart S.C (s₀ + 1 + 1) = M.slotStart S.C (s₀ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hanc := hA
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hanc
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hk4 : 4 * Δ S * 4 ≤ 4 * Δ S * (S.C.k + 2) := Nat.mul_le_mul_left _ (by omega)
  have hk2 : 4 * Δ S * S.C.k ≤ 4 * Δ S * (S.C.k + 2) := Nat.mul_le_mul_left _ (by omega)
  have hk8 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 8 * Δ S := by ring
  -- `tGAT` is far enough before the slot: the anchor is at most the start of slot `s₀ + 1`
  have hcut : tGAT + 4 * Δ S * (S.C.k + 2) + 2 * Δ S ≤ M.supportCutoff S.C s₀ + 4 * Δ S := by omega
  have hm2 : tGAT + max (2 * Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
    rcases max_choice (2 * Δ S) Δs with h | h <;> rw [h] <;> omega
  have hm1 : tGAT + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hEs : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hpA : p ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (s₀ + 1)) :=
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEs hp
  obtain ⟨kp, hlp, hsp⟩ := id hB
  obtain ⟨-, hkp1, hkp2⟩ := E.tick_active kp p _ hlp
  have hTp : x.tickInput p (M.slotStart S.C (s₀ + 1)) = x.st kp p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hlp]
  -- the members of slot `s₀ + 1`: honest at the support cutoff of slot `s₀ + 2`, active from `tGAT` to it
  have hwH : ∀ w ∈ Hon M S A x (s₀ + 1), w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    fun w hw => (Finset.mem_sdiff.1 hw).2
  have hwA : ∀ w ∈ Hon M S A x (s₀ + 1), w ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (s₀ + 1 + 1)) :=
    fun w hw => (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEs2 (hwH w hw)
  have hdw0 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s₀ hA
  have hdw1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1) hAnchor
  -- each member ticks to the vote time of slot `s₀ + 1`, active up to that tick from its tick to `tGAT + Δ S`
  have hwR : ∀ w ∈ Hon M S A x (s₀ + 1),
      w ∈ A.activeThroughoutToTick x ((tGAT + Δ S : ℕ) : ℤ) (M.voteTime S.C (s₀ + 1)) := by
    intro w hw
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega)
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
    exact ⟨kw, hkwl, (tickStep_eq_of_lbl M) x E hkwl, (E.tick_active kw w _ hkwl).2.2⟩
  -- the voters of the slot `s₀`
  have hMaj0 := (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x _ s₀ hCommittees hA hEs
  have hVot0 : ∀ u ∈ S.P.committee s₀ ∩ Hon M S A x s₀, ∃ vote : GoldfishVote V,
      ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    have hHA := (hActive s₀ (by omega) hEs u (Finset.mem_sdiff.1 huH).2).1
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x R s₀ u E
      ((voteTime_tick_window_of_honestActiveAt M F U) S A x R s₀ u E hSkew hHA)
    obtain ⟨vote, -, -, hsent⟩ := (honest_votes_of_window M F U) S A x R s₀ u E hl hAw hK
    exact ⟨vote, k', hl, hsent⟩
  set anchor := M.get_anchor (x.tickInput p (M.slotStart S.C (s₀ + 1))) ((M.slotStart S.C (s₀ + 1) : ℕ) : Int)
    with hanchor
  set Hs0 : Finset V := S.P.committee s₀ ∩ Hon M S A x s₀ with hHs0
  have hex : ∀ u ∈ Hs0, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s₀)).tree ∧ anchor.AncestorEq H_u := by
    intro u hu
    obtain ⟨vote, i', hl, hsent⟩ := hVot0 u hu
    obtain ⟨H_u, hT, hvt, hAH⟩ := hPrev u hu vote ⟨i', hl, hsent⟩
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
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    rw [hHf u hu]
    refine ⟨hK, ?_, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
    intro w hw
    obtain ⟨kw, -, hkw, hkwt⟩ := hkw w hw
    rw [hkw]
    refine Activity.not_mem_corruptedAtTime.1 (Finset.mem_sdiff.1 huH).2 kw ?_
    have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
    linarith
  have hOnly : ∀ w ∈ Hon M S A x (s₀ + 1), ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C (s₀ + 1))).tree,
      B₁.slot = s₀ + 1 → B₁ = B := by
    intro w hw B₁ hB₁ hslot
    obtain ⟨kw, -, hkw, hkwt⟩ := hkw w hw
    have hpk : p ∉ A.corrupted kw := by
      refine Activity.not_mem_corruptedAtTime.1 hp kw ?_
      have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
      linarith
    have hB₁' : B₁ ∈ (x.st kw w).tree := by
      have := hB₁
      unfold Trace.tickInput at this
      rw [hkw] at this
      exact this
    exact (GoldilocksCorrectness.Record.Proofs.Executions.only_block_of_unforgeability_st M F U) S A x R E (s₀ + 1)
      kw B B₁ p w hpk rfl hB hB₁' hslot
  have hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C (s₀ + 1))).tree, B₁.root ≠ B.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold M x)]
    exact ⟨B₁, hB₁, heq⟩
  -- `head_height_floor` at the proposer's tick to the slot's start is at most each member's at its tick to the vote
  -- time: `floor_le_of_delivery_ticks` from `a := slotStart (s₀ + 1) − Δ S − max (Δ S) Δs`, with the member's
  -- earlier tick to the start of slot `s₀ + 1`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hpk : p ∉ A.corrupted kp := E.not_mem_corrupted_of_tick hlp
  have hslotp : ∀ Y ∈ (x.st kp p).tree, M.slotStart S.C Y.slot ≤ M.slotStart S.C (s₀ + 1) := by
    intro Y hY
    have h₁ := (slot_le_clockValue_of_mem_tree M F) R E hpk hY
    have h₂ : S.C.slot ((x.clockValue kp p : ℕ) : Int) ≤ S.C.slot ((M.slotStart S.C (s₀ + 1) : ℕ) : Int) :=
      GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
        (by exact_mod_cast E.clockValue_le_of_set hpk (Or.inl hlp))
    have h₃ : M.slot S.C (M.slotStart S.C (s₀ + 1)) < s₀ + 1 + 1 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout F.sched) S (by omega)
    rw [hsl] at h₃
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (Nat.lt_succ_iff.1 (lt_of_le_of_lt (h₁.trans h₂) h₃))
  have hFloorW : ∀ w ∈ Hon M S A x (s₀ + 1),
      M.head_height_floor (x.tickInput p (M.slotStart S.C (s₀ + 1))) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))) ≤
        (M.chainStateOf S.C B.parent).h := by
    intro w hw
    refine ⟨?_, (hBase1 w hw).2⟩
    obtain ⟨kw, hkwl, hkw', hkwt⟩ := hkw w hw
    have hkwE : x.time kw ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
      have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
      linarith
    set a : ℕ := M.slotStart S.C (s₀ + 1) - Δ S - max (Δ S) Δs with ha
    have haT : tGAT ≤ a := by omega
    obtain ⟨hk₂, -, -⟩ := (tickStep_spec M) x R E (t := M.slotStart S.C (s₀ + 1)) (v := w) (by omega)
      (Activity.mem_activeThroughout_of_le
        (by
          have h1 : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show tGAT + Δ S ≤ M.slotStart S.C (s₀ + 1) by omega)
          push_cast at h1 ⊢; linarith)
        (by
          have h1 : ((M.slotStart S.C (s₀ + 1) + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
          push_cast at h1 ⊢; linarith)
        (hwA w hw))
    have hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kw → w ∈ A.active i := by
      intro i h1 h2
      have h0 : ((tGAT : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast haT
      exact Activity.mem_activeThroughout.1 (hwA w hw) i (le_trans (R.time_mono h2) hkwE)
        (le_trans h0 (le_trans h1 (R.time_mono (Nat.le_succ i))))
    have hak : (a : ℝ) ≤ x.time kp := by
      have : ((a + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (show a + Δ S ≤ _ by omega)
      push_cast at this
      linarith
    have hv₀ : p ∈ A.activeThroughout x a (a + Δs) := by
      refine Activity.mem_activeThroughout_of_le (by exact_mod_cast haT) ?_ hpA
      exact_mod_cast (show a + Δs ≤ M.supportCutoff S.C (s₀ + 1) by omega)
    have hfl := (floor_le_of_delivery_ticks M F U Fx) S A x R GST (M.slotStart S.C (s₀ + 1)) kp a
      (M.voteTime S.C (s₀ + 1)) (M.slotStart S.C (s₀ + 1)) kw (x.tickStep w (M.slotStart S.C (s₀ + 1))) p w E hNet
      hSkew hRedeliver Sy hRoots hParent (hThird.mono (le_trans hkwE (by exact_mod_cast hEs2))) (by omega) (by omega)
      hlp hak hv₀ hkwl (by omega) hwin hk₂ (by omega) hslotp
      (by
        have : ((M.voteTime S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.voteTime S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
        linarith)
      (by omega)
    have hTw : x.tickInput w (M.voteTime S.C (s₀ + 1)) = x.st kw w := by
      unfold Trace.tickInput
      rw [hkw']
    rw [hTp, hTw]
    exact hfl
  have hHeadP := (anchor_has_viable_head_st M F) S A x R E kp p
    (x.tickInput p (M.slotStart S.C (s₀ + 1))).lockEntries ((M.slotStart S.C (s₀ + 1) : ℕ) : Int)
  rw [← hTp, ← GoldilocksCorrectness.Record.get_anchor_eq_anchorAt F.rd] at hHeadP
  -- the start of the windows of the proposer and the members, `tGAT + Δ S`
  have htStart : (((tGAT + Δ S : ℕ) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s₀ + 1 - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rw [Nat.add_sub_cancel]
    have hN1 : tGAT + 4 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
    have hN2 : tGAT + Δs + 2 * Δ S ≤ M.supportCutoff S.C s₀ := by omega
    have hN1R : ((tGAT + 4 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN2R : ((tGAT + Δs + 2 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by exact_mod_cast hN2
    push_cast at hN1R hN2R
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    have hm : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s₀ := by omega
    rw [Nat.cast_sub hm]
    push_cast
    have := max_lt (show (2 * (Δ S : ℝ)) < (M.supportCutoff S.C s₀ : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
      ΔClockBehind by linarith) (show (Δs : ℝ) < (M.supportCutoff S.C s₀ : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
      ΔClockBehind by linarith)
    linarith
  have hpR : p ∈ A.activeThroughoutToTick x ((tGAT + Δ S : ℕ) : ℤ) (M.slotStart S.C (s₀ + 1)) := by
    have hle : tGAT + Δ S ≤ M.slotStart S.C (s₀ + 1) := by omega
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega) (by exact_mod_cast hle) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hpA
    · push_cast; linarith
    · have : ((M.slotStart S.C (s₀ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (s₀ + 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1) by omega)
      linarith
  have hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s₀ + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s₀ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    rw [show (((M.slotStart S.C (s₀ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) =
      ((M.slotStart S.C (s₀ + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) by push_cast; ring]
    exact Activity.mem_activeThroughout_of_le (by exact_mod_cast (show tGAT ≤ _ by omega))
      (by exact_mod_cast (show _ ≤ M.supportCutoff S.C (s₀ + 1) by omega)) hpA
  have hHold : ∀ u ∈ Hs0, u ∈ A.activeThroughout x
      ((M.supportCutoff S.C (s₀ + 1 - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₀ + 1 - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro u hu
    rw [Nat.add_sub_cancel, show (((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) =
      ((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) by push_cast; ring]
    have hu' := (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2
    refine Activity.mem_activeThroughout_of_le (by exact_mod_cast (show tGAT ≤ _ by omega))
      (by exact_mod_cast (show _ ≤ M.supportCutoff S.C (s₀ + 1) by
        have := le_max_right (2 * Δ S) Δs; omega))
      ((mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEs hu')
  obtain ⟨hHeld, hVote, hBne⟩ := (round_base_votes_upTo M F U) S A x R GST (s₀ + 1) (Hon M S A x (s₀ + 1)) Hs0 Hf
    anchor B p _ (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C (s₀ + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C (s₀ + 1))))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C (s₀ + 1))))
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    (votesCastByOwner_of_unforgeability M F S A x R E) (by omega)
    (by rw [Nat.add_sub_cancel]; omega)
    ((tGAT + Δ S : ℕ) : ℤ) htStart hpR hHoldP hwR ⟨kp, hlp, hsp⟩ hHsPrev hHold
    (fun w _ votes support_votes hCV =>
      ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R E s₀
        (x.tickStep w (M.voteTime S.C (s₀ + 1))) (Hon M S A x s₀) w hMaj0).2.2 votes support_votes hCV)
    (ancestorEq_refl _) hBase3 hOnly hRootNew
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) hFloorW
    (fun w hw => (hBase1 w hw).1) hHeadP
  exact ⟨hHeld, hVote, hBne⟩

/-- **At C3's round, an updater whose finalized block is on the proposal's chain saves the proposal.** Under the
hypotheses of C3 with clauses 1 and 3 of `RoundBaseAt` (as `healed_round_votes_upTo`), for a set `Upd` of updaters of
slot `s` each with its finalized block at its tick to the support cutoff of slot `s + 1` `B` or an ancestor of `B`:
every member of `Upd` saves `B` as its confirmation of slot `s` at that tick, every lock entry its revocation of slot
`s + 1` leaves is compatible with `B`, and its update makes `B` fast.

Why: `round_base_updates_upTo` with the honest voters `Hs` the committee's members of `Hon M S A x s`, each an honest
active validator and an updater of slot `s` (`hActive`), outside the adversary set at every honest validator's tick to
the support cutoff of slot `s + 1` (`honestActiveAt`'s second exclusion), and voting for `B`
(`healed_round_votes_upTo`); the counts from the committee's majority (`hCommittees`). Nothing is read of a member of
`Upd` after its own tick, so a member may be in the adversary set at the real time of the support cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- as `healed_round_votes_upTo`'s; `Upd`: the updaters read.

Read aloud: at a round whose base's first and third clauses hold, every updater of the round's first slot whose
finalized block is on the proposal's chain confirms the proposal, makes it fast and keeps no lock off its chain. -/
theorem healed_round_updates_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s + 1))
    (hA : anchorCW S tGAT ≤ M.slotStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hBase1 : ∀ w ∈ Hon M S A x s, (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h)
    (hBase3 : ∀ w ∈ Hon M S A x s, ∀ (n₁ : M.N) (sent₁ : List (NamedObject V)),
      .ok (n₁, sent₁) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n₁, M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e = true →
        e.B.AncestorEq B.parent)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon M S A x (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (M.get_anchor (x.tickInput (S.P.proposer s) (M.slotStart S.C s))
          ((M.slotStart S.C s : ℕ) : Int)).AncestorEq H_u)
    -- the updaters read, each with its finalized block at its tick to the support cutoff of slot `s + 1` on `B`'s chain
    (Upd : Finset V) (hUpdU : ∀ v ∈ Upd, v ∈ updaterAt M S A x s)
    (hFinU : ∀ v ∈ Upd, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) :
    (∀ v ∈ Upd,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    (∀ w ∈ Upd, ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'', e.B.compatible B = true) ∧
    (∀ v ∈ Upd, ∃ n'' : M.N,
      ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation =
        M.savedConfirmation n'' ∧ B ∈ M.fastBlocks n'') := by
  obtain ⟨hHeld, hVote, hBne⟩ := (healed_round_votes_upTo M F U Fx) S A x R GST tGAT tAwakeEnd s B E hNet hSkew
    hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive hCommittees hs1 hAnchor hA hEnd hp hB hBase1 hBase3
    hNoCol hPrev
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  have hk := S.C.k_ge_two
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hss : M.slotStart S.C (s₀ + 1) = M.slotStart S.C s₀ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  have hanc := hA
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hanc
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hk8 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 8 * Δ S := by ring
  have hm1 : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s₀ + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hEs2 : M.supportCutoff S.C (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  have hdw1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1) hAnchor
  have hAct : ∀ v ∈ Hon M S A x (s₀ + 1), v ∈ honestActiveAt M S A x (s₀ + 1) ∧ v ∈ updaterAt M S A x (s₀ + 1) :=
    fun v hv => hActive (s₀ + 1) (by omega) hEs2 v (Finset.mem_sdiff.1 hv).2
  have hMaj1 := (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x _ (s₀ + 1)
    hCommittees hAnchor hEs2
  have hHs' : ∀ v ∈ Upd, ∀ u ∈ S.P.committee (s₀ + 1) ∩ Hon M S A x (s₀ + 1), u ∈ S.P.committee (s₀ + 1) ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s₀ + 1 + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s₀ + 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₀ + 1) B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C (s₀ + 1))).tree := by
    intro v hv u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    have hvU : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₀ + 1 + 1))
        (M.supportCutoff S.C (s₀ + 1 + 1)) := hUpdU v hv
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x R (s₀ + 1) u E
      ((voteTime_tick_window_of_honestActiveAt M F U) S A x R (s₀ + 1) u E hSkew (hAct u huH).1)
    obtain ⟨vote, -, -, hsent⟩ := (honest_votes_of_window M F U) S A x R (s₀ + 1) u E hl hAw hK
    have hvt := hVote u huH vote ⟨k', hl, hsent⟩
    rw [hvt] at hsent
    exact ⟨hK, (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E hvU
      (fun hX => (Finset.mem_sdiff.1 (hAct u huH).1).2 (Finset.mem_union_right _ hX)),
      ⟨k', hl, hsent⟩, hHeld u huH⟩
  exact (round_base_updates_upTo M F U) S A x R GST (s₀ + 1) Upd (S.P.committee (s₀ + 1) ∩ Hon M S A x (s₀ + 1)) B
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent (votesCastByOwner_of_unforgeability M F S A x R E) (by omega) hm1
    hUpdU (fun u hu => (hAct u (Finset.mem_inter.1 hu).2).2) hHs'
    (fun v _ => ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R E (s₀ + 1)
      (x.tickStep v (M.supportCutoff S.C (s₀ + 1 + 1))) (Hon M S A x (s₀ + 1)) v hMaj1).2.1)
    ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R E (s₀ + 1) 0
      (Hon M S A x (s₀ + 1)) (S.P.proposer (s₀ + 1)) hMaj1).1
    hBne hFinU

end GoldilocksCorrectness.Record.Proofs.Executions
