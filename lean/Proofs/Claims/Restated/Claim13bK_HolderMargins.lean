import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_CrossTransport
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Chain-in-tree facts from a held block

The chain-in-tree fact `ConeAnchorChainInTree` at the readers of a slot, obtained from a block an
honest validator holds early enough or from an eligible confirmation, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every block strictly between an honest active reader's SG root and `B` is in that reader's
    slot-`(s + 1)` voter tree, the same holds for every ancestor `X` of `B`. -/
theorem coneAnchorChainInTree_mono (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {X B : Block V} {s : Slot}
    (hXB : Block.Preceq X B) (h : Restated.ConeAnchorChainInTree M S x B s) :
    Restated.ConeAnchorChainInTree M S x X s := by
  intro v mr hv hmr nv hnv A hA C hAC hne hCX Tt hTt
  exact h v mr hv hmr nv hnv A hA C hAC hne (preceq_trans_Preceq hCX hXB) Tt hTt

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the invariant holds at round `r` with anchor `T`, and `D` is a named block in play whose
    erasure is a descendant of `T`'s, then `T`'s chain-state height is at most `D`'s. -/
theorem derive_height_le_of_anchor_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    {D : NamedBlock V} (hD : Restated.blockInLog M S Sched x D) (hTD : Block.Preceq T.erase D.erase) :
    (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg D).h :=
  facts.cs.derive_height_mono S.E S.cfg
    (Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hinv.inPlay hD hTD)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `v_1` holds `B` at a step at or after `tGAT` and more than a delay before slot `s`'s view
    freeze, `X` is an ancestor of `B` and a descendant of `T`, and every tick of an honest active
    member of slot `(s + 1)`'s committee before that slot's vote instant has an outcome
    (`hneTickW`), then every block strictly between an honest active reader's SG root and `X` is in
    that reader's slot-`(s + 1)` voter tree. -/
theorem coneAnchorChainInTree_of_heldDescendant (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {B : NamedBlock V} {v_1 : V} {m : Nat} (hBv_1 : B ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    {X : Block V} (hXB : Block.Preceq X B.erase) (hTX : Block.Preceq T.erase X)
    {s : Slot} (hdeadline : (x[m].time : Int) + S.E.Δ < M.view_freeze S.E s)
    (hj : s + 1 ≤ (M.opening_slot S.hc (r + 1)) + 1)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x X s :=
  Restated.coneAnchorChainInTree_mono facts S x hXB
    (Restated.coneAnchorChainInTree_of_holder facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hBv_1 hv_1 hm
      (preceq_trans_Preceq hTX hXB)
      (Restated.derive_height_le_of_anchor_preceq facts S Sched x hexec hinv
        (Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hBv_1) (preceq_trans_Preceq hTX hXB))
      hdeadline hj hneTickW)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every slot `s`, `slotStart s + 2Δ ≤ support_cutoff s`. -/
private theorem slotStart_add_two_delta_le_support_cutoff_holder (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s := by
  have hd := S.E.Δ_pos
  have hvt := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hp0 : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
    slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
      (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
  have hpv := facts.sch.proposal_time_lt_vote_time S.E s
  have hc0 : slotStart S.E.Δ s ≤ M.support_cutoff S.E s :=
    slotStart_le_of_le_slotOf S (le_of_lt (facts.sch.support_cutoff_pos S s))
      (le_of_eq (facts.sch.slotOf_support_cutoff S.E s).symm)
  have hcp := facts.sch.support_cutoff_ne_proposal_time S.E s
  have hcv := facts.sch.support_cutoff_ne_vote_time S.E s
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero (slotStart_emod_delta S s)
  obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E s)
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  rw [ha, hb] at hp0
  rw [← hvt, ha, hb] at hpv
  rw [ha, hc] at hc0
  rw [hc, hb] at hcp
  rw [← hvt, hc, ha] at hcv
  rw [ha, hc]
  have hab : a ≤ b := le_of_mul_le_mul_left hp0 hd
  have hba : b < a + 1 :=
    lt_of_mul_lt_mul_left (by rw [mul_add, mul_one]; exact hpv) (le_of_lt hd)
  have hbeq : b = a := by omega
  subst hbeq
  have hac : b ≤ c := le_of_mul_le_mul_left hc0 hd
  have hc1 : c ≠ b := fun h => hcp (by rw [h])
  have hc2 : c ≠ b + 1 := fun h => hcv (by rw [h, mul_add, mul_one])
  have hc3 : b + 2 ≤ c := by omega
  nlinarith

/-- For every slot `s`, `support_cutoff s + Δ ≤ view_freeze s`. -/
private theorem support_cutoff_add_delta_le_view_freeze_holder (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  have hd := S.E.Δ_pos
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  have hlt := facts.sch.Sts_support_cutoff_lt_view_freeze S.E s
  rw [hk, hc] at hlt
  rw [hk, hc]
  have hck : c < (k : Int) := by
    by_contra hcon
    have h1 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) (le_of_lt hd)
    rw [mul_comm] at h1
    linarith
  have hck1 : c + 1 ≤ (k : Int) := hck
  have h2 : S.E.Δ * (c + 1) ≤ S.E.Δ * (k : Int) :=
    mul_le_mul_of_nonneg_left hck1 (le_of_lt hd)
  rw [mul_add, mul_one] at h2
  rw [mul_comm (k : Int)]
  linarith

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_hm {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_hm {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

open scoped DC in
/-- The lift of the set `s` can return `a` exactly when `a` is a member of `s`. -/
private theorem returns_lift_iff_hm {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- Every outcome of the slot-`s` confirmation votes of `st` is, for an outcome `tm` of `st`'s
    resolution times, the slot-`s` pool filtered by `tm` against the support cutoff and then by the
    absence of a second vote of the same signer in the late set. -/
private theorem confVotes_cases_hm (E : Env V) (st : M.S) (s : Slot) {e : Finset (GoldfishVote V)}
    (he : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e) :
    ∃ tm, st.tau ⇢ tm ∧
      e = (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) := by
  obtain ⟨e', he', rfl⟩ := returns_map_elim_hm _ _ _ he
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_hm _ _ _ he'
  exact ⟨tm, htm, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `q` is awake from one delay before slot `s`'s start to its confirmation instant and honest
    through it, some outcome of `q`'s slot-`s` confirmation eligibility test passes `H`, and `q`'s
    ticks in that window have an outcome (`hneTickq`), then at the tick step `nc` at slot `s`'s
    support cutoff `q` is honest through `nc` and holds a named block whose erasure is a descendant
    of `H`. -/
theorem supporterHead_held_before_cut (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (htd : Restated.TimeDiverges M x)
    {s : Slot} {n : Nat} {q : V} {H : Block V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][q].st).st.core s ⇢ el)
    (hel : el H = true)
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out) :
    ∃ (nc : Nat) (Xn : NamedBlock V), Restated.tickStepAt M x nc (M.support_cutoff S.E s) ∧
      Xn ∈ (x[nc][q].st).st.bodies ∧ Restated.HonestThrough M Sched x nc q ∧
      Block.Preceq H Xn.erase := by
  have hd := S.E.Δ_pos
  have hsc : slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s :=
    slotStart_add_two_delta_le_support_cutoff_holder facts S s
  have hsccf : M.support_cutoff S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Sts_support_cutoff_le_confirmation_time S.E s
  obtain ⟨u, hu, hel2⟩ := (returns_bind_iff_hm _ _ _).1 hel'
  obtain ⟨sc, hscs, hel3⟩ := (returns_bind_iff_hm _ _ _).1 hel2
  have hsc' : ∀ B, M.goldfish_score S.E (x[n][q].st).st.core.T u u s B ⇢ sc B :=
    (returns_lift_iff_hm _ _).1 hscs
  have hel4 := (Record.returns_pure _ _).1 hel3
  rw [hel4] at hel
  have hlt := of_decide_eq_true hel
  have helig : M.voters_count S.E (Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s) s <
      2 * sc H := by
    simp only [Restated.Vocabulary.Protocol.confCount] at hlt
    omega
  obtain ⟨tm, htm, hueq⟩ := confVotes_cases_hm S.E _ s hu
  have hel5 : beforeCutoff tm (M.support_cutoff S.E s) ((x[n][q].st).st.core.pool s) ⊆
      Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s := by
    intro u' hu'
    have h := (mem_beforeCutoff_iff _ _ _ _).mp hu'
    refine (mem_beforeCutoff_iff _ _ _ _).mpr ⟨h.1, ?_⟩
    obtain ⟨σ, hσ, hlt⟩ :=
      exists_stamp_of_stampedBefore (facts.sto.stampedBefore_vote_of_tau _ tm htm h.2)
    exact stampedBefore_of_lt hσ (lt_of_lt_of_le hlt
      (WithBot.coe_le_coe.mpr (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s)))
  obtain ⟨tS, htS⟩ : ∃ tS : GoldfishVote V → Bool,
      ∀ u', M.targets_under (x[n][q].st).st.core.T H u' ⇢ tS u' :=
    ⟨fun u' => (facts.fc.targets_under_nonempty _ H u').choose,
      fun u' => (facts.fc.targets_under_nonempty _ H u').choose_spec⟩
  obtain ⟨sS, hsS⟩ := facts.fc.raw_supporters_nonempty (x[n][q].st).st.core.T u u s H
  have hmaj := (facts.fc.confirmation_adoption hel5 hueq tS htS tS htS
    (fun u' hu' h => Or.inl ⟨hu', h⟩)
    (fun u' hu' => by
      rw [hueq] at hu'
      exact Or.inl (hel5 (Finset.mem_filter.mp hu').1))
    (sc H) (hsc' H) helig sS hsS sS hsS).2
  obtain ⟨y, hy⟩ : sS.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨-, u0, huy, -, htar⟩ := (facts.fc.mem_supporters_iff (_E := S.E) sS hsS tS htS).mp hy
  have hu0 : u0 ∈ u := ((facts.sch.mem_votes_by_iff _ _ _).mp huy).1
  have hu0' : u0 ∈ beforeCutoff tm (M.support_cutoff S.E s) ((x[n][q].st).st.core.pool s) := by
    rw [hueq] at hu0
    exact (Finset.mem_filter.mp hu0).1
  have hpool : u0 ∈ (M.store_pool (x[n][q].st).st.core s) := ((mem_beforeCutoff_iff _ _ _ _).mp hu0').1
  have hus : u0.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x n q hpool
  have hpool' : u0 ∈ (M.store_pool (x[n][q].st).st.core u0.slot) := by rw [hus]; exact hpool
  obtain ⟨X, hX, hXs, hHX⟩ := (facts.fc.targets_under_iff (tS u0) (htS u0)).mp htar
  have hXT : X ∈ (x[n][q].st).st.core.T := Proofs.HealingLemmas.find?_mem hX
  obtain ⟨τ, hτ, -⟩ := Restated.stamp_le_clock_gfVote facts S Sched x n q hpool'
  obtain ⟨σ, hσ, -⟩ := Restated.stamp_le_clock_block facts S Sched x n q hXT
  have hearly : max τ σ < ((M.support_cutoff S.E s : Int) : Stamp) := by
    obtain ⟨σ', hσ', hlt⟩ := exists_stamp_of_stampedBefore ((mem_beforeCutoff_iff _ _ _ _).mp hu0').2
    rw [facts.sto.tau_eq_max _ hX hXs hτ hσ tm htm] at hσ'
    cases hσ'
    exact hlt
  have hσlt : σ < ((M.support_cutoff S.E s : Int) : Stamp) :=
    lt_of_le_of_lt (le_max_right _ _) hearly
  have hqc : q ∈ Sched.awake (M.support_cutoff S.E s) \
      Sched.adv (M.support_cutoff S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hqaw (by linarith)
      hsccf, hqh _ hsccf⟩
  obtain ⟨Xn, hXn, hXne⟩ := Restated.exists_named_of_mem_tree facts S Sched x n q hXT
  obtain ⟨nc, hnc⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.support_cutoff_pos S s)
  have hσ' : (x[n][q].st).st.core.timestamp_block Xn.erase = some σ := by rw [hXne]; exact hσ
  have hXnc : Xn ∈ (x[nc][q].st).st.bodies :=
    Restated.body_held_before_cut facts S Sched x hXn hσ' hσlt hnc hqc (facts.sch.support_cutoff_emod_delta S s)
      (hneTickq nc _ hnc (facts.sch.support_cutoff_emod_delta S s) hqc (by linarith) hsccf)
  have hncself := (Restated.tickStepAt_time facts x hnc).2
  have hqnc : Restated.HonestThrough M Sched x nc q := fun t ht =>
    hqh t (by linarith)
  refine ⟨nc, Xn, hnc, hXnc, hqnc, ?_⟩
  rw [hXne]
  exact preceq_eq_true_iff_Preceq.mp hHX

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If some outcome of an honest reader `q`'s slot-`s` confirmation eligibility test passes `H`, `X`
    is an ancestor of `H` and a descendant of `T`, slot `s` starts at or after `tGAT`, slot `s + 1`
    is at most one slot after round `r + 1`'s opening slot, and the ticks of `hneTickq` and
    `hneTickW` have outcomes, then every block strictly between an honest active reader's SG root
    and `X` is in that reader's slot-`(s + 1)` voter tree. -/
theorem coneAnchorChainInTree_of_eligibleConfirmation (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {s : Slot} {nq : Nat} {q : V} {H X : Block V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[nq][q].st).st.core s ⇢ el)
    (hel : el H = true)
    (hXH : Block.Preceq X H) (hTX : Block.Preceq T.erase X)
    (hlo : tGAT ≤ slotStart S.E.Δ s)
    (hj : s + 1 ≤ (M.opening_slot S.hc (r + 1)) + 1)
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x X s := by
  obtain ⟨nc, Xn, hnc, hXn, hqnc, hHXn⟩ :=
    Restated.supporterHead_held_before_cut facts S Sched x htd hqaw hqh el hel' hel hneTickq
  have hd := S.E.Δ_pos
  have hncself := (Restated.tickStepAt_time facts x hnc).2
  have hsc : slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s :=
    slotStart_add_two_delta_le_support_cutoff_holder facts S s
  have hvf : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s :=
    support_cutoff_add_delta_le_view_freeze_holder facts S s
  exact Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hXn hqnc (by linarith)
    (preceq_trans_Preceq hXH hHXn) hTX (by linarith) hj hneTickW

end

end DecoupledConsensusModel.Sts.Restated
