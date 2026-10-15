import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeHeadsUpTo
import Proofs.Claims.Restated.Claim13bK_CrossTransport
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bStepKitRelayUpTo
import Proofs.Claims.Restated.Claim13bSyncViewUpTo
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_6
import Proofs.Claims.Restated.Claim13beRoute3_7
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitRelayUpTo
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Honest heads follow a confirmed block into the next slot, with synchrony up to a bound

The theorems carrying the Goldfish votes a validator counts at slot `s`'s confirmation to the vote
duty of every member of `HonSlot S Sched (s + 1)`, and the heads at slot `s + 1` and at the second
slot of round `r + 1`, with synchrony assumed only up to the instant each theorem needs.
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

/-- Synchrony from wake up to a bound `b'` gives it up to every bound `b ≤ b'`. -/
private theorem syncBefore_mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

/-- For `0 < s`, slot `s`'s support cutoff is `slotStart s + 2Δ`. -/
private theorem support_cutoff_eq_of_pos_headsUpTo (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

/-- For every slot `s`, `support_cutoff s + Δ ≤ view_freeze s`. -/
private theorem support_cutoff_add_delta_le_view_freeze_headsUpTo (facts : Record.Facts M)
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

/-- For every slot `s`, `view_freeze s < confirmation_time s`. -/
private theorem view_freeze_lt_confirmation_time_headsUpTo (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    M.view_freeze S.E s < M.confirmation_time S.E s := by
  have hd := S.E.Δ_pos
  have h1 := facts.sch.view_freeze_lt_vote_time_succ S.E s
  have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
  have h3 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s
  have h4 := slotStart_succ S.E.Δ s
  linarith

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_hnu {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_hnu {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_hnu {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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
/-- The lift of the set `s` can return `a` exactly when `a ∈ s`. -/
private theorem returns_lift_iff_hnu {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- Every outcome of `confVotes` at slot `s` is the slot-`s` pool filtered, for an outcome `tm` of
    `st`'s resolution times, against the support cutoff, and then by the absence of a second vote of
    the same signer in the late set. -/
private theorem confVotes_cases_hnu (E : Env V) (st : M.S) (s : Slot) {e : Finset (GoldfishVote V)}
    (he : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e) :
    ∃ tm, st.tau ⇢ tm ∧
      e = (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) := by
  obtain ⟨e', he', rfl⟩ := returns_map_elim_hnu _ _ _ he
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_hnu _ _ _ he'
  exact ⟨tm, htm, rfl⟩

/-- Every outcome of `voteReadOf` at slot `s` is made of `before`'s store with its clock set to slot
    `s`'s vote instant, `before`'s signing record, and an outcome of the phase tick at that instant
    on `before`'s cache. -/
private theorem voteReadOf_cases_hnu (S : Setup V) (before : M.N) (s : Slot) {n : M.N}
    (hn : Restated.voteReadOf M S before s ⇢ n) :
    ∃ c : M.Cache, M.onPhaseTick S.E S.hc before.st.core.toHealing (M.vote_time S.E s)
        before.cache ⇢ c ∧
      n = M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c := by
  obtain ⟨c, hc, hcn⟩ := returns_map_elim_hnu _ _ _ hn
  exact ⟨c, hc, hcn.symm⟩

/-- Every outcome of `gfHeadWith` is an outcome of `M.get_head_in_tree_with` over an outcome of
    `st`'s voter tree and outcomes of its two voter views, for the slot before `st`'s own. -/
private theorem gfHeadWith_cases_hnu (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) {H : Block V} (hH : Restated.gfHeadWith M contract E hc st ⇢ H) :
    ∃ T, Restated.voteTreeOf M E st ⇢ T ∧ ∃ W, Restated.voteViewOf M E st ⇢ W ∧
      ∃ U, Restated.voteSupportViewOf M E st ⇢ U ∧
        M.get_head_in_tree_with contract E hc st T W U (st.s - 1) ⇢ H := by
  unfold Restated.gfHeadWith at hH
  obtain ⟨T, hT, hH⟩ := (returns_bind_iff_hnu _ _ _).1 hH
  obtain ⟨W, hW, hH⟩ := (returns_bind_iff_hnu _ _ _).1 hH
  obtain ⟨U, hU, hH⟩ := (returns_bind_iff_hnu _ _ _).1 hH
  exact ⟨T, hT, W, hW, U, hU, hH⟩

/-- Every vote in an outcome of `confVotes` at slot `s` is in the store's slot-`s` pool. -/
private theorem confVotes_subset_pool_headsUpTo (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e → e ⊆ M.store_pool st s := by
  intro e he u hu
  obtain ⟨tm, -, rfl⟩ := confVotes_cases_hnu E st s he
  rw [Finset.mem_filter, mem_beforeCutoff_iff] at hu
  exact hu.1.1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to slot `s`'s view freeze: if `q` is awake from one delay before slot `s`'s
    start to its confirmation instant and honest through it, `w` is a member of
    `HonSlot S Sched (s + 1)`, `mr` is the tick step at slot `(s + 1)`'s vote instant, and `T` is an
    ancestor of `D`, then every vote `u` that `q`'s store after `n` steps counts at slot `s`'s
    confirmation, with its head resolving in `q`'s tree to a descendant of `D`, is in the support
    view of `w`'s slot-`(s + 1)` vote duty with its head resolving in `w`'s tree to a descendant of
    `D`, or `w`'s raw view holds two votes of `u`'s signer. -/
theorem adoptionForward_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} (hsync : Restated.SynchronyFromWakeBefore M S x (M.view_freeze S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {T D : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR T)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR T)
    (hTD : Block.Preceq T D)
    (hs : 0 < s) (hlo : tGAT ≤ slotStart S.E.Δ s)
    (hsR : M.view_freeze S.E s ≤ tR)
    {n : Nat} {q : V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    {mr : Nat} {w : V} (hmr : Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)))
    (hw : w ∈ Restated.HonSlot M S Sched (s + 1))
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      t < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (x[n][q].st).st.core s ⇢ e →
    ∀ W, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W →
    ∀ U, Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U →
    ∀ u ∈ e, ∀ b : Bool, M.targets_under (x[n][q].st).st.core.T D u ⇢ b → b = true →
      (u ∈ U ∧ ∀ b' : Bool,
          M.targets_under (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T D u ⇢ b' →
          b' = true) ∨
        M.equivocates W u.val_index = true := by
  intro e he W hW U hU u hu b hb htar
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
      support_cutoff_eq_of_pos_headsUpTo facts S.E hs
  have hvflo : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s :=
      support_cutoff_add_delta_le_view_freeze_headsUpTo facts S s
  have hvfhi : M.view_freeze S.E s < M.vote_time S.E (s + 1) :=
      facts.sch.view_freeze_lt_vote_time_succ S.E s
  have hsccf : M.support_cutoff S.E s ≤ M.confirmation_time S.E s :=
      facts.sch.Sts_support_cutoff_le_confirmation_time S.E s
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have hct1 : M.confirmation_time S.E (s + 1) = slotStart S.E.Δ s + 10 * S.E.Δ := by
    have h1 := slotStart_succ S.E.Δ s
    have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
    linarith
  have hvt1 : M.vote_time S.E (s + 1) = slotStart S.E.Δ s + 5 * S.E.Δ := by
    have h1 := slotStart_succ S.E.Δ s
    have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
    linarith
  have hss2 : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
    have h1 := slotStart_succ S.E.Δ s
    have h2 := slotStart_succ S.E.Δ (s + 1)
    rw [show s + 2 = s + 1 + 1 from rfl]
    linarith
  obtain ⟨-, hmrself⟩ := Restated.tickStepAt_time facts x hmr
  rw [hvt1] at hmrself
  have hgsts : S.E.t_GST ≤ slotStart S.E.Δ s := le_trans hgst hlo
  have hwh : Restated.HonestThrough M Sched x mr w :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hw (by rw [hct1]; linarith)
  have hwadv : w ∉ Sched.adv (x[mr].time : Int) := hwh _ le_rfl
  have hwwin := Restated.honSlot_succ_window facts S Sched hw
  have hwslot : w ∉ Sched.adv (slotStart S.E.Δ s) := by
    intro hin
    exact ((Restated.mem_HonSlot facts).mp hw).2.2 (hmono _ _ (by rw [hct1]; linarith) hin)
  have hpool : u ∈ (M.store_pool (x[n][q].st).st.core s) :=
    confVotes_subset_pool_headsUpTo S.E _ s e he hu
  have hus : u.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x n q hpool
  have hpool' : u ∈ (M.store_pool (x[n][q].st).st.core u.slot) := by rw [hus]; exact hpool
  obtain ⟨X, hX, hXs, hDX⟩ := (facts.fc.targets_under_iff b hb).mp htar
  have hXT : X ∈ (x[n][q].st).st.core.T := Proofs.HealingLemmas.find?_mem hX
  have hXroot : X.root = u.head := Proofs.HealingLemmas.find?_root hX
  obtain ⟨τ, hτ, -⟩ := Restated.stamp_le_clock_gfVote facts S Sched x n q hpool'
  obtain ⟨σ, hσ, -⟩ := Restated.stamp_le_clock_block facts S Sched x n q hXT
  have hearly : max τ σ < ((M.support_cutoff S.E s : Int) : Stamp) := by
    obtain ⟨tm, htm, rfl⟩ := confVotes_cases_hnu S.E _ s he
    rw [Finset.mem_filter, mem_beforeCutoff_iff] at hu
    obtain ⟨σ', hσ', hlt⟩ := exists_stamp_of_stampedBefore hu.1.2
    rw [facts.sto.tau_eq_max _ hX hXs hτ hσ tm htm] at hσ'
    cases hσ'
    exact hlt
  have hτlt : τ < ((M.support_cutoff S.E s : Int) : Stamp) :=
    lt_of_le_of_lt (le_max_left _ _) hearly
  have hσlt : σ < ((M.support_cutoff S.E s : Int) : Stamp) :=
    lt_of_le_of_lt (le_max_right _ _) hearly
  obtain ⟨i, hin, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool'
  obtain ⟨hst1, -, hcomm⟩ := Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1
  have hstn := Restated.stamp_mono_sts facts S Sched x q (Nat.succ_le_of_lt hin) hst1
  rw [hτ] at hstn
  have hτeq : τ = (((x[i + 1][q].st).st.core.t : Int) : Stamp) := Option.some.inj hstn
  have hclk : (x[i + 1][q].st).st.core.t < M.support_cutoff S.E s := by
    rw [hτeq] at hτlt; exact WithBot.coe_lt_coe.mp hτlt
  have hqc : q ∈ Sched.awake (M.support_cutoff S.E s) \
      Sched.adv (M.support_cutoff S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hqaw (by rw [hsc]; linarith)
      (by rw [hsc, hct]; linarith), hqh _ (by rw [hsc, hct]; linarith)⟩
  have hti : (x[i + 1].time : Int) < M.support_cutoff S.E s :=
    Restated.time_lt_of_clock_lt facts S Sched x htd (facts.sch.support_cutoff_pos S s)
      (facts.sch.support_cutoff_emod_delta S s) hqc hclk
      (fun nc' hnc' => hneTickq nc' _ hnc' (facts.sch.support_cutoff_emod_delta S s) hqc
        (by rw [hsc]; linarith) hsccf)
  have hlo_i : slotStart S.E.Δ u.slot ≤ (x[i + 1].time : Int) :=
    Restated.slotStart_le_time_of_flip_gfVote facts S Sched x h0 h1
  rw [hus] at hlo_i
  have htsucc := Restated.time_succ_le facts S Sched x i
  have hii : (x[i].time : Int) ≤ (x[i + 1].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_succ i)
  have hqi : Restated.HonestThrough M Sched x i q := fun t ht =>
    hqh t (by rw [hsc] at hti; rw [hct]; linarith)
  have hawi : AtomicAwake x i w :=
    mem_awake_of_awakeThroughout Sched hwwin (by linarith) (by rw [hsc] at hti; linarith)
  have hmax : max (x[i + 1].time : Int) S.E.t_GST = (x[i + 1].time : Int) :=
    max_eq_left (by linarith)
  obtain ⟨k, -, hk1, hk⟩ :=
    Restated.gfVote_in_pool_of_accepts_upTo facts S Sched x
      ((Restated.gfVoteRelayAtAcceptBefore_of_sync facts S Sched x hsync).mono
        (by rw [hmax]; linarith)) htd h0 h1
      hqi hawi hcomm (by rw [hus]; exact hs) (by rw [hus]; exact hlo_i)
      (by rw [hus, hmax]; exact awakeThroughout_mono Sched hwwin (by linarith)
            (by rw [hsc] at hti; linarith))
      (by rw [hus]; exact hwslot)
      (by rw [hus, hmax, hss2]; rw [hsc] at hti; linarith)
      (fun n' hn' => hneTickw n' _ hn' (slotStart_emod_delta S u.slot)
        (by
          rw [hus]
          exact Finset.mem_sdiff.2
            ⟨mem_awake_of_awakeThroughout Sched hwwin (by linarith) (by linarith), hwslot⟩)
        (by rw [hus, hvt1]; linarith))
  rw [hmax] at hk1
  have hkt : (x[k].time : Int) < M.view_freeze S.E s := by linarith
  have hkmr : k < mr := Restated.step_lt_of_time_lt facts S Sched x (by linarith)
  obtain ⟨Xn, hXn, hXne⟩ := Restated.exists_named_of_mem_tree facts S Sched x n q hXT
  obtain ⟨nc, hnc⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.support_cutoff_pos S s)
  have hσ' : (x[n][q].st).st.core.timestamp_block Xn.erase = some σ := by rw [hXne]; exact hσ
  have hXnc : Xn ∈ (x[nc][q].st).st.bodies :=
    Restated.body_held_before_cut facts S Sched x hXn hσ' hσlt hnc hqc (facts.sch.support_cutoff_emod_delta S s)
      (hneTickq nc _ hnc (facts.sch.support_cutoff_emod_delta S s) hqc (by rw [hsc]; linarith) hsccf)
  have hncself := (Restated.tickStepAt_time facts x hnc).2
  have hqnc : Restated.HonestThrough M Sched x nc q := fun t ht =>
    hqh t (by rw [hct]; rw [hsc] at hncself; linarith)
  have hTX : Block.Preceq T Xn.erase := by rw [hXne]; exact preceq_trans_Preceq hTD (preceq_eq_true_iff_Preceq.mp hDX)
  obtain ⟨hXw, σw, hσw, hσwlt⟩ :=
    Restated.block_in_tree_of_holder_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hawake hthird hcs hlen hunder
      hunderS (mr := mr) (v := w) hXnc hqnc hTX
      (by rw [hsc] at hncself; linarith) (by linarith) hsR
      (by linarith) hwadv
      (awakeThroughout_mono Sched hwwin (by rw [hsc] at hvflo; linarith) (by linarith))
      (fun n' t' hn' hΔ hq _ ht' => hneTickw n' t' hn' hΔ hq (by linarith))
  rw [hXne] at hXw hσw
  have hfindw : Block.find? (x[mr][w].st).st.core.T u.head = some X := by
    rw [← hXroot]; exact Restated.find_of_mem_tree_honest facts S Sched x hexec hwh hXw
  have hstT : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T = (x[mr][w].st).st.core.T := by
    rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]
  have htarw : ∀ b' : Bool,
      M.targets_under (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T D u ⇢ b' → b' = true :=
    fun b' hb' => (facts.fc.targets_under_iff b' hb').mpr ⟨X, by rw [hstT]; exact hfindw, hXs, hDX⟩
  rcases hk with ⟨hkpool, τw, hτw, hτwle⟩ | heq
  · left
    have hpoolmr : u ∈ (M.store_pool (x[mr][w].st).st.core u.slot) :=
      Restated.mem_pool_mono_sts facts S Sched x w (Nat.succ_le_of_lt hkmr) hkpool
    have hτmr := Restated.stamp_mono_sts facts S Sched x w (Nat.succ_le_of_lt hkmr) hτw
    rw [hus] at hpoolmr
    refine ⟨?_, htarw⟩
    have hU' := hU
    simp only [Restated.voteSupportViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)]
      at hU'
    exact facts.sch.mem_voter_support_view_of_pool S.E _ s
      (by rw [Record.Model.GS.pool, facts.sto.toHealing_gs_pool]; rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_pool]; exact hpoolmr)
      (by rw [facts.sto.toHealing_gs_timestamp_vote]; rw [Restated.voteStoreAt, facts.hd.setClock_core_timestamp_vote]
          exact hτmr)
      (lt_of_le_of_lt hτwle (WithBot.coe_lt_coe.mpr hkt))
      (by rw [facts.sto.toHealing_gs_T, hstT]; exact hfindw) hXs
      (by rw [facts.sto.toHealing_gs_timestamp_block]; rw [Restated.voteStoreAt, facts.hd.setClock_core_timestamp_block]
          exact hσw) hσwlt U hU'
  · right
    refine facts.sch.equivocates_mono ?_ u.val_index heq
    intro u' hu'
    have hu's : u'.slot = u.slot := Restated.slot_of_mem_pool_sts facts S Sched x k w hu'
    have hu'' : u' ∈ (M.store_pool (x[k][w].st).st.core u'.slot) := by rw [hu's]; exact hu'
    obtain ⟨τ', hτ', hτ'le⟩ := Restated.stamp_le_clock_gfVote facts S Sched x k w hu''
    have hclkk := Restated.clock_le_time_sts facts S Sched x k w
    have hmr' : u' ∈ (M.store_pool (x[mr][w].st).st.core s) := by
      rw [← hus, ← hu's]
      exact Restated.mem_pool_mono_sts facts S Sched x w (le_of_lt hkmr) hu''
    have hτ'mr := Restated.stamp_mono_sts facts S Sched x w (le_of_lt hkmr) hτ'
    have hW' := hW
    simp only [Restated.voteViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)] at hW'
    exact facts.fc.mem_voter_view_of_pool S.E _ s
      (by rw [Record.Model.GS.pool, facts.sto.toHealing_gs_pool]; rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_pool]; exact hmr')
      (by rw [facts.sto.toHealing_gs_timestamp_vote]; rw [Restated.voteStoreAt, facts.hd.setClock_core_timestamp_vote]
          exact hτ'mr)
      (lt_of_le_of_lt hτ'le (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclkk hkt))) W hW'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to the send's deadline `max (x[k].time) t_GST + Δ`: if step `k` is an honest
    send of a Goldfish vote `u` of a member of its slot's committee, `u`'s slot is positive, the
    send is at or after the slot's start, `w` is awake from the slot's start to the deadline and not
    held at the slot's start, and the deadline is at or before the start of the slot two later, then
    at some delivery step `d` before the deadline `u` enters `w`'s pool with a stamp at or before
    `d`'s instant, or `w`'s pool holds two votes of `u`'s signer. -/
theorem gfVote_in_pool_of_honestSend_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max (x[k].time : Int) S.E.t_GST + S.E.Δ))
    (htd : Restated.TimeDiverges M x) {p w : V} {u : GoldfishVote V}
    (hsend : Restated.HonestSendAt M S x k (⟨p, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)))
    (hcomm : u.val_index ∈ S.E.committee u.slot) (hpos : 0 < u.slot)
    (hlo : slotStart S.E.Δ u.slot ≤ (x[k].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ u.slot))
    (hhi : max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤ slotStart S.E.Δ (u.slot + 2))
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ u.slot) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ u.slot) x[n] w) (slotStart S.E.Δ u.slot) ⇢ out) :
    ∃ d : Nat, (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ ∧
      ((u ∈ (M.store_pool (x[d + 1][w].st).st.core u.slot) ∧
          ∃ τ : Stamp, (x[d + 1][w].st).st.core.timestamp_vote u = some τ ∧
            τ ≤ ((x[d].time : Int) : Stamp)) ∨
        M.equivocates ((M.store_pool (x[d][w].st).st.core u.slot)) u.val_index = true) := by
  obtain ⟨d, -, hlbl, hkd, hd1⟩ := Restated.synchronyFromWake_from_step_upTo facts S hsync hsend
    (awakeThroughout_mono Sched hawT hlo le_rfl)
  refine ⟨d, hkd, hd1, ?_⟩
  have hlod : slotStart S.E.Δ u.slot ≤ (x[d].time : Int) := le_trans hlo hkd
  have hwin := Restated.gf_window_of_awakeThroughout facts S Sched x htd d w u
    (awakeThroughout_mono Sched hawT le_rfl (le_of_lt hd1)) hwh hlod hpos
    (lt_of_lt_of_le hd1 hhi) hneTick
  have hclk := Restated.clock_le_time_sts facts S Sched x d w
  rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl hwin hcomm
      (facts.nd.process_nonempty _ _ _ (fun _ h => by cases h)) with hmem | heq | ⟨hm1, hst⟩
  · refine Or.inl ⟨Restated.mem_pool_mono_sts facts S Sched x w (Nat.le_succ d) hmem, ?_⟩
    obtain ⟨τ, hτ, hτle⟩ := Restated.stamp_le_clock_gfVote facts S Sched x d w hmem
    exact ⟨τ, Restated.stamp_mono_sts facts S Sched x w (Nat.le_succ d) hτ,
      le_trans hτle (WithBot.coe_le_coe.mpr hclk)⟩
  · exact Or.inr heq
  · exact Or.inl ⟨hm1, _, hst, WithBot.coe_le_coe.mpr hclk⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to slot `s`'s confirmation instant, under the hypotheses of
    `adoptionForward_afterPhase_upTo`: every vote of every raw view that `w`'s slot-`(s + 1)` vote
    duty can build is in `q`'s late view `confLate` of slot `s`, or that late view holds two votes
    of its signer. -/
theorem adoptionBackward_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} (hsync : Restated.SynchronyFromWakeBefore M S x (M.confirmation_time S.E s))
    (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption)
    (hs : 0 < s) (hgsts : S.E.t_GST ≤ slotStart S.E.Δ s)
    {n : Nat} {q : V} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    {mr : Nat} {w : V} (hmr : Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)))
    (hw : w ∈ Restated.HonSlot M S Sched (s + 1))
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out) :
    ∀ W, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W →
    ∀ u ∈ W,
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s ∨
        M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s) u.val_index
          = true := by
  intro W hW u hu
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have hct1 : M.confirmation_time S.E (s + 1) = slotStart S.E.Δ s + 10 * S.E.Δ := by
    rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]; ring
  have hvt1 : M.vote_time S.E (s + 1) = slotStart S.E.Δ s + 5 * S.E.Δ := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time, slotStart_succ]; ring
  have hss1 : slotStart S.E.Δ (s + 1) = slotStart S.E.Δ s + 4 * S.E.Δ := slotStart_succ S.E.Δ s
  have hss2 : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
    rw [slotStart_add]; push_cast; ring
  obtain ⟨-, hmrself⟩ := Restated.tickStepAt_time facts x hmr
  rw [hvt1] at hmrself
  obtain ⟨-, hnself⟩ := Restated.tickStepAt_time facts x hn
  rw [hct] at hnself
  have hwh : Restated.HonestThrough M Sched x mr w :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hw (by rw [hct1]; linarith)
  have hqslot : q ∉ Sched.adv (slotStart S.E.Δ s) := hqh _ (by rw [hct]; linarith)
  have hvalid := Restated.voteSetValid_phase facts S Sched x hexec (s := s) (mr := mr) (v := w)
    W hW
  have hsl : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1 = s := by
    simp only [Restated.voteStoreAt_slot facts, Nat.add_sub_cancel]
  rw [hsl] at hvalid
  obtain ⟨hus, hcomm⟩ := hvalid u hu
  have hcomm' : u.val_index ∈ S.E.committee u.slot := by rw [hus]; exact hcomm
  have hpos : 0 < u.slot := by rw [hus]; exact hs
  have hneq : ∀ n' : Nat, Restated.tickStepAt M x n' (slotStart S.E.Δ u.slot) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (slotStart S.E.Δ u.slot) x[n'] q)
          (slotStart S.E.Δ u.slot) ⇢ out :=
    fun n' h => hneTickq n' _ h (slotStart_emod_delta S u.slot)
      (by
        rw [hus]
        exact Finset.mem_sdiff.2
          ⟨mem_awake_of_awakeThroughout Sched hqaw (by linarith) (by rw [hct]; linarith), hqslot⟩)
      (le_of_eq (congrArg (slotStart S.E.Δ) hus.symm))
      (by rw [hus, hct]; linarith)
  have hsend_case : ∀ k : Nat,
      Restated.HonestSendAt M S x k (⟨w, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) →
      slotStart S.E.Δ s ≤ (x[k].time : Int) → (x[k].time : Int) ≤ (x[mr].time : Int) →
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s ∨
        M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s) u.val_index
          = true := by
    intro k hsend hklo hkhi
    have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) :=
      max_eq_left (by linarith)
    obtain ⟨d, -, hd1', hdk⟩ := Restated.gfVote_in_pool_of_honestSend_upTo facts S Sched x
      (syncBefore_mono (by rw [hmax, hct]; linarith) hsync) htd hsend
      hcomm' hpos (by rw [hus]; exact hklo)
      (by rw [hus, hmax]; exact awakeThroughout_mono Sched hqaw (by linarith)
            (by rw [hct]; linarith))
      (by rw [hus]; exact hqslot)
      (by rw [hus, hmax, hss2]; linarith) hneq
    rw [hmax] at hd1'
    exact Restated.confLate_of_pool_at facts S Sched x (Restated.step_lt_of_time_lt facts S Sched x (by linarith)) hus
      (by rw [hct]; linarith) hdk
  have hpool_case : ∀ m : Nat, m ≤ mr → u ∈ (M.store_pool (x[m][w].st).st.core u.slot) →
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s ∨
        M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s) u.val_index
          = true := by
    intro m hm hmem
    obtain ⟨i, him, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hmem
    have hlo_i : slotStart S.E.Δ u.slot ≤ (x[i + 1].time : Int) :=
      Restated.slotStart_le_time_of_flip_gfVote facts S Sched x h0 h1
    have hi1 : (x[i + 1].time : Int) ≤ (x[mr].time : Int) :=
      Restated.time_mono_int facts S Sched x (le_trans (Nat.succ_le_of_lt him) hm)
    have htsucc := Restated.time_succ_le facts S Sched x i
    have hii : (x[i].time : Int) ≤ (x[i + 1].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.le_succ i)
    rw [hus] at hlo_i
    have hwi : Restated.HonestThrough M Sched x i w := fun t ht =>
      hwh t (le_trans ht (by linarith))
    have hawi : AtomicAwake x i q :=
      mem_awake_of_awakeThroughout Sched hqaw (by linarith) (by rw [hct]; linarith)
    have hmax : max (x[i + 1].time : Int) S.E.t_GST = (x[i + 1].time : Int) :=
      max_eq_left (by linarith)
    obtain ⟨k, -, hk1, hk⟩ :=
      Restated.gfVote_in_pool_of_accepts_upTo facts S Sched x
        ((Restated.gfVoteRelayAtAcceptBefore_of_sync facts S Sched x hsync).mono
          (by rw [hmax, hct]; linarith)) htd
        h0 h1 hwi hawi hcomm' hpos (by rw [hus]; exact hlo_i)
        (by rw [hus, hmax]; exact awakeThroughout_mono Sched hqaw (by linarith)
              (by rw [hct]; linarith))
        (by rw [hus]; exact hqslot)
        (by rw [hus, hmax, hss2]; linarith) hneq
    rw [hmax] at hk1
    exact Restated.confLate_of_pool_at facts S Sched x (Restated.step_lt_of_time_lt facts S Sched x (by linarith)) hus
      (by rw [hct]; linarith) hk
  have hW' : M.voter_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ W := by
    have h := hW
    simp only [Restated.voteViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)] at h
    exact h
  rcases facts.fc.voter_view_cases _ _ _ W hW' hu with hu | hu
  · have hu1 := hu.1
    rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_pool, Restated.voteStoreAt,
      facts.hd.ModelProperties_setClock_core_pool] at hu1
    exact hpool_case mr le_rfl (by rw [hus]; exact hu1)
  · obtain ⟨Bl, hBl, hBls, huv, -⟩ := hu
    have hBlT : Bl ∈ (x[mr][w].st).st.core.T := by
      rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt,
        facts.hd.ModelProperties_setClock_core_T] at hBl
      exact hBl
    obtain ⟨Dn, hDn, hDne⟩ := Restated.exists_named_of_mem_tree facts S Sched x mr w hBlT
    have huD : u ∈ Dn.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes, hDne]; exact huv
    have hgen : Dn ≠ NamedBlock.genesis := by
      intro hcon
      rw [hcon, named_genesis_gf_votes] at huD
      exact absurd huD List.not_mem_nil
    have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st
        (NamedObject.block Dn) = false := by
      rw [Record.st_zero M S Sched x w]
      simp only [Restated.Vocabulary.Execution.Object.processed, facts.nd.initial_st,
        facts.hd.initial_bodies, Finset.mem_singleton]
      exact decide_eq_false hgen
    obtain ⟨i, him, hf0, hf1⟩ :=
      Restated.exists_flip_of_processed facts S Sched x w (NamedObject.block Dn) h0
        (decide_eq_true hDn)
    have hbodyi : Dn ∈ (x[i + 1][w].st).st.bodies := of_decide_eq_true hf1
    have hmemi : Dn.erase ∈ (x[i + 1][w].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x (i + 1) w]
      exact Finset.mem_image_of_mem NamedBlock.erase hbodyi
    have hslo := Restated.slotStart_le_time_of_mem_tree facts S Sched x (i + 1) w hmemi
    rw [hDne, hBls, hss1] at hslo
    have hi1 : (x[i + 1].time : Int) ≤ (x[mr].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt him)
    rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
      ⟨m, hl, -, -, hpay⟩ | ⟨τ, hl, -, -, hem⟩
    · rcases hpay with hmsg | ⟨B, -, hcc⟩
      · have ho : NamedObject.gfVote u ∈ relayedObjects m.msg := by
          rw [hmsg, mem_relayedObjects_iff]
          exact Or.inr (Or.inl ⟨u, huD, rfl⟩)
        have hsend := Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho
          (Restated.receipt_outcome_of_flip facts S Sched x hl hf0 hf1)
        have hdt : x[i + 1].time = x[i].time := Restated.deliver_time facts S Sched x hl
        have hdt' : (x[i + 1].time : Int) = (x[i].time : Int) := by exact_mod_cast hdt
        exact hsend_case i hsend (by linarith) (by linarith)
      · exact hcc.elim
    · obtain ⟨out₁, hout₁, -, hem'⟩ := hem
      rcases hem' with hemit | ⟨B, -, hcc⟩
      · exact hpool_case i (le_of_lt him)
          (Restated.mem_pool_of_mem_tick_block facts S Sched x i w τ out₁ hout₁ hemit huD)
      · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to slot `s`'s confirmation instant, under the hypotheses of
    `adoptionForward_afterPhase_upTo`: `Restated.Vocabulary.Protocol.AdoptionTransport` holds at `D`
    from `q`'s tree, every outcome of the votes it counts at slot `s` and its late view, to `w`'s
    tree and every raw and support view of `w`'s slot-`(s + 1)` vote duty. -/
theorem adoptionTransport_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} (hsync : Restated.SynchronyFromWakeBefore M S x (M.confirmation_time S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {T D : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR T)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR T)
    (hTD : Block.Preceq T D)
    (hs : 0 < s) (hlo : tGAT ≤ slotStart S.E.Δ s)
    (hsR : M.view_freeze S.E s ≤ tR)
    {n : Nat} {q : V} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    {mr : Nat} {w : V} (hmr : Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)))
    (hw : w ∈ Restated.HonSlot M S Sched (s + 1))
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      t < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (x[n][q].st).st.core s ⇢ e →
    ∀ W, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W →
    ∀ U, Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U →
    Restated.Vocabulary.Protocol.AdoptionTransport M (x[n][q].st).st.core.T (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T
      e (Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s) W U D :=
  fun e he W hW U hU =>
  ⟨Restated.adoptionForward_afterPhase_upTo facts S Sched x hexec
      (syncBefore_mono (le_of_lt (view_freeze_lt_confirmation_time_headsUpTo facts S s)) hsync)
      hmult htd hmono hgst hcv hawake hthird hcs hlen
      hunder hunderS hTD hs hlo hsR hqaw hqh hmr hw hneTickq hneTickw e he W hW U hU,
    Restated.adoptionBackward_afterPhase_upTo facts S Sched x hexec hsync htd hmono hs (le_trans hgst hlo) hn hqaw hqh
      hmr hw hneTickq W hW⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to slot `s`'s confirmation instant: if `n` is the tick step at that instant,
    `q` is awake from one delay before slot `s`'s start to it and honest through it, some outcome of
    the slot-`s` confirmation eligibility test of `q`'s store passes `C`, `T ⪯ D ⪯ C`, and
    `ConeAnchorCompatible` and `ConeAnchorChainInTree` hold at `D` and `s`, then `HeadsBelow` holds
    for `D` at slot `s + 1`: every member of `HonSlot S Sched (s + 1)` votes there for a descendant
    of `D`. -/
theorem headsBelow_succ_of_eligible_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} (hsync : Restated.SynchronyFromWakeBefore M S x (M.confirmation_time S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {T D C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR T)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR T)
    (hTD : Block.Preceq T D) (hDC : Block.Preceq D C)
    (hs : 0 < s) (hlo : tGAT ≤ slotStart S.E.Δ s)
    (hsR : M.view_freeze S.E s ≤ tR)
    {n : Nat} {q : V} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][q].st).st.core s ⇢ el)
    (hel : el C = true)
    (hAB : Restated.ConeAnchorCompatible M S x D s) (hpath : Restated.ConeAnchorChainInTree M S x D s)
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t : Int),
      Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t → t < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    Restated.HeadsBelow M S Sched x D (s + 1) := by
  intro w mr hw hmr G hG
  obtain ⟨u, hu, hel2⟩ := (returns_bind_iff_hnu _ _ _).1 hel'
  obtain ⟨sc, hsc, hel3⟩ := (returns_bind_iff_hnu _ _ _).1 hel2
  have hsc' : ∀ B, M.goldfish_score S.E (x[n][q].st).st.core.T u u s B ⇢ sc B :=
    (returns_lift_iff_hnu _ _).1 hsc
  have hel4 := (Record.returns_pure _ _).1 hel3
  rw [hel4] at hel
  have hlt := of_decide_eq_true hel
  have hCD : sc C ≤ sc D :=
    Restated.confScore_le_of_preceq facts S.E (x[n][q].st).st.core s hDC u hu (sc C) (hsc' C)
      (sc D) (hsc' D)
  have helig : M.voters_count S.E (Restated.Vocabulary.Protocol.confLate M S.E (x[n][q].st).st.core s) s <
      2 * sc D := by
    simp only [Restated.Vocabulary.Protocol.confCount] at hlt
    omega
  unfold Restated.gfHeadFrom at hG
  obtain ⟨nv, hnv, hG⟩ := (returns_bind_iff_hnu _ _ _).1 hG
  obtain ⟨Tt, hTt, W, hW, U, hU, hGh⟩ := gfHeadWith_cases_hnu _ _ _ _ hG
  obtain ⟨c, -, hneq⟩ := voteReadOf_cases_hnu S (x[mr][w].st) (s + 1) hnv
  have hcore : nv.st = M.store_with_cache (M.ns_setClock S.E (x[mr][w].st).st (M.vote_time S.E (s + 1))) c := by
    rw [hneq, facts.nd.mkNode_st]
  rw [hcore] at hTt hW hU hGh
  simp only [Restated.voteTreeOf, Restated.voteViewOf, Restated.voteSupportViewOf, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hTt hW hU hGh
  change Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ Tt at hTt
  change Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W at hW
  change Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U at hU
  change M.get_head_in_tree_with (M.gradeContract nv.cache) S.E S.hc (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) Tt W U ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) ⇢ _ at hGh
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).toHealing
    (M.round_of S.hc (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s)
  have hGf := (facts.hd.get_head_in_tree_with_eq_fork_choice _ _ _ _ _ _ _ _ R hR G).1 hGh
  have hT := Restated.adoptionTransport_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono
    hgst hcv hawake hthird hcs hlen hunder hunderS hTD hs hlo hsR hn hqaw hqh hmr hw hneTickq
    (hneTickW w hw) u hu W hW U hU
  obtain ⟨tm, htm, hueq⟩ := confVotes_cases_hnu S.E _ s hu
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
      ∀ u', M.targets_under (x[n][q].st).st.core.T D u' ⇢ tS u' :=
    ⟨fun u' => (facts.fc.targets_under_nonempty _ D u').choose,
      fun u' => (facts.fc.targets_under_nonempty _ D u').choose_spec⟩
  obtain ⟨tT, htT⟩ : ∃ tT : GoldfishVote V → Bool,
      ∀ u', M.targets_under (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T D u' ⇢ tT u' :=
    ⟨fun u' => (facts.fc.targets_under_nonempty _ D u').choose,
      fun u' => (facts.fc.targets_under_nonempty _ D u').choose_spec⟩
  have hfwd : ∀ u' ∈ u, tS u' = true →
      (u' ∈ U ∧ tT u' = true) ∨ M.equivocates W u'.val_index = true := by
    intro u' hu' h
    rcases hT.forward u' hu' (tS u') (htS u') h with ⟨h1, h2⟩ | h3
    · exact Or.inl ⟨h1, h2 (tT u') (htT u')⟩
    · exact Or.inr h3
  obtain ⟨sS, hsS⟩ := facts.fc.raw_supporters_nonempty (x[n][q].st).st.core.T u u s D
  obtain ⟨sT, hsT⟩ := facts.fc.raw_supporters_nonempty
    (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T W U s D
  have hmaj := (facts.fc.confirmation_adoption hel5 hueq tS htS tT htT hfwd hT.backward
    (sc D) (hsc' D) helig sS hsS sT hsT).2
  have hsl : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1 = s := by
    simp only [Restated.voteStoreAt_slot facts, Nat.add_sub_cancel]
  have hsub : U ⊆ W :=
    facts.fc.voter_support_view_subset S.E _ _
      (fun Bl hBl => (Restated.treeBlock_carried_ok facts S Sched x hexec mr w (by
        rw [Restated.voteStoreAt, facts.hd.setClock_toHealing_T] at hBl
        exact hBl)).1) U hU W hW
  rw [hsl] at hGf
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hsub sT hsT hmaj
    (hAB w mr hw hmr nv hnv R hR)
    (fun _ C' h1 h2 h3 => hpath w mr hw hmr nv hnv R hR C' h1 h2 h3 Tt hTt) G hGf

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Stamping a store's clock does not change the outcomes of the confirmation eligibility test for
    slot `s`. -/
private theorem confEligible_setClock_headsUpTo (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Int) (s : Slot) :
    Restated.Vocabulary.Protocol.confEligible M E (M.ns_setClock E st t).core s
      = Restated.Vocabulary.Protocol.confEligible M E st.core s := by
  have htau : (M.ns_setClock E st t).core.tau = st.core.tau :=
    facts.sto.tau_eq_of_fields (facts.hd.Sts_setClock_core_T E st t)
      (facts.hd.setClock_core_timestamp_block E st t) (facts.hd.setClock_core_timestamp_vote E st t)
  have hpool : (M.ns_setClock E st t).core.pool s = st.core.pool s :=
    facts.hd.Sts_setClock_core_pool E st t s
  unfold Restated.Vocabulary.Protocol.confEligible
    Restated.Vocabulary.Protocol.confCount Restated.Vocabulary.Protocol.confVotes
    Restated.Vocabulary.Protocol.confEarly Restated.Vocabulary.Protocol.confLate
  rw [htau, hpool, facts.hd.setClock_core_timestamp_vote, facts.hd.Sts_setClock_core_T]

/-- For every store `hs` the round-`r₁` action can give from `before`, `hs.live_confirmed` either
    passes some outcome of the confirmation eligibility test of `before`'s store for the slot before
    the action instant's, or is the `confRoot` of `before`'s store with its clock set to the action
    instant. -/
private theorem actionHealingStore_live_confirmed_cases_headsUpTo (facts : Record.Facts M)
    (S : Setup V) (before : M.N) (r₁ : Round) (hs : M.HS)
    (hhs : hs ∈ Restated.actionHealingStore M S before r₁) :
    (∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E before.st.core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) ⇢ el ∧
        el hs.live_confirmed = true) ∨
      hs.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core := by
  classical
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed]
  by_cases hroot : X.live_confirmed = Restated.Vocabulary.Protocol.confRoot M
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
  · exact Or.inr hroot
  · left
    obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing
      (M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.s)
    obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.T
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) B ⇢ score B :=
      ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
        fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
    obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
      (M.get_filtered_block_tree
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing.toFG)
      score
      (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B))
    have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    rcases hwalk with hwalk | hfg
    · rcases hgen with ⟨-, -, hel⟩ | hfg
      · refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
          (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B), ?_, ?_⟩
        · rw [← confEligible_setClock_headsUpTo facts S.E before.st
            (Restated.Vocabulary.Execution.Setup.a M S r₁)]
          refine (returns_bind_iff_hnu _ _ _).2 ⟨_, returns_map_intro_hnu _ _ _
            (returns_map_intro_hnu _ _ _ htm), ?_⟩
          refine (returns_bind_iff_hnu _ _ _).2 ⟨score, (returns_lift_iff_hnu _ _).2 hscore, ?_⟩
          exact (Record.returns_pure _ _).2 rfl
        · rw [hwalk]
          exact hel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

/-- With synchrony up to `S.a (r + 1)`: if `n` is the tick step at `S.a (r + 1)`, `q` is in
    `HonRound S Sched (r + 1)` and a store its round-`(r + 1)` action can give holds `C` as
    `live_confirmed`, `T ⪯ D ⪯ C`, the `confRoot` of `q`'s store is an ancestor of `T`, `HeadsBelow`
    holds for `T` at the second slot of round `r + 1`, and `ConeAnchorCompatible` and
    `ConeAnchorChainInTree` hold at `D`, then `HeadsBelow` holds for `D` at that slot. -/
theorem headsBelow_secondSlot_of_confirmed_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {n : Nat} {q : V} {T : NamedBlock V} {D C : Block V}
    (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR T.erase)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR T.erase)
    (hlo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hsR : M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) ≤ tR)
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hq : q ∈ Restated.HonRound M S Sched (r + 1))
    (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S (x[n][q].st) (r + 1))
    (hC : hs.live_confirmed = C)
    (hTD : Block.Preceq T.erase D) (hDC : Block.Preceq D C)
    (hroot : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][q].st) ((M.opening_slot S.hc (r + 1))))) T.erase)
    (hprevT : Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1)) + 1))
    (hAB : Restated.ConeAnchorCompatible M S x D ((M.opening_slot S.hc (r + 1))))
    (hpath : Restated.ConeAnchorChainInTree M S x D ((M.opening_slot S.hc (r + 1))))
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) ≤ t →
      t ≤ M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (M.opening_slot S.hc (r + 1) + 1),
      ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      t < M.vote_time S.E (M.opening_slot S.hc (r + 1) + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    Restated.HeadsBelow M S Sched x D ((M.opening_slot S.hc (r + 1)) + 1) := by
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn' : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn
  have hqaw := Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hq
  have hqA : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hq).2
  have hqh : HonestThroughTime Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))
      q := fun t' ht' hin => hqA (hmono _ _ (by rw [← hct]; exact ht') hin)
  have hcases := actionHealingStore_live_confirmed_cases_headsUpTo facts S (x[n][q].st) (r + 1) hs hhs
  rw [Restated.slotOf_a_sub_one facts S (r + 1), hC] at hcases
  rcases hcases with ⟨el, hel', hel⟩ | hCroot
  · exact Restated.headsBelow_succ_of_eligible_afterPhase_upTo facts S Sched x hexec
      (syncBefore_mono (le_of_eq hct) hsync) hmult htd hmono hgst hcv hawake
      hthird hcs hlen hunder
      hunderS hTD hDC (facts.gr.opening_slot_pos S (Nat.succ_pos r)) hlo hsR hn' hqaw hqh
      el hel' hel hAB hpath hneTickq hneTickW
  · intro w mr hw hmr G hG
    have hCT : Block.Preceq C T.erase := by
      rw [Restated.confStoreAt, hct] at hroot
      rw [hCroot]; exact hroot
    exact preceq_trans_Preceq (preceq_trans_Preceq hDC hCT) (hprevT w mr hw hmr G hG)

end

end DecoupledConsensusModel.Sts.Restated
