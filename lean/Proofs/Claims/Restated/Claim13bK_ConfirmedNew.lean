import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.Claim13bK_GradePairwise
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepPairwise
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Confirmed blocks at the next round's action read

Two honest confirmation reads of one slot see each other's counted votes and pass compatible blocks;
from this, the confirmed blocks, the grade-pairwise condition and the graded descendants at the
action read of a round after the switch round. Stated over a model `M : Record.Model V` and its
facts.
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

/-- For a positive slot `s`, `support_cutoff s = slotStart s + 2Δ`. -/
private theorem support_cutoff_eq_of_pos_confNew (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_cn {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_cn {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_cn {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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
private theorem returns_lift_iff_cn {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- The finality-gadget source read at a node state has an outcome. -/
private theorem actionFGSource_nonempty_cn (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff_cn _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- If slot `s` is positive and starts at or after GST, `n` is the tick step at its confirmation
    instant, `v` and `w` are awake from one delay before slot `s`'s start to that instant and honest
    through it, and the ticks named by `hneTickv` and `hneTickw` have an outcome, then every vote of
    an outcome `votes` of the votes `v`'s store counts at slot `s` after `n` steps is in `w`'s late
    view of slot `s`, or that late view holds two votes of its signer. -/
theorem confVotes_transfer_confLate_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    {s : Slot} (hs : 0 < s) (hgsts : S.E.t_GST ≤ slotStart S.E.Δ s)
    {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    {v w : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hwaw : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hwh : HonestThroughTime Sched (M.confirmation_time S.E s) w)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out)
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes) :
    ∀ u ∈ votes,
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s ∨
        M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s) u.val_index
          = true := by
  intro u hu
  obtain ⟨e, he, rfl⟩ := returns_map_elim_cn _ _ _ hvotes
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_cn _ _ _ he
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos_confNew facts S.E hs
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have hss2 : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
    have h1 := slotStart_succ S.E.Δ s
    have h2 := slotStart_succ S.E.Δ (s + 1)
    rw [show s + 2 = s + 1 + 1 from rfl]
    linarith
  obtain ⟨-, hnself⟩ := Restated.tickStepAt_time facts x hn
  rw [hct] at hnself
  have hu' := hu
  rw [Finset.mem_filter] at hu'
  have he := hu'.1
  rw [mem_beforeCutoff_iff] at he
  have hpool : u ∈ (M.store_pool (x[n][v].st).st.core s) := he.1
  have hstv := facts.sto.stampedBefore_vote_of_tau _ tm htm he.2
  have hus : u.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x n v hpool
  have hpool' : u ∈ (M.store_pool (x[n][v].st).st.core u.slot) := by rw [hus]; exact hpool
  obtain ⟨i, hin, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool'
  obtain ⟨hst1, -, hcomm⟩ := Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1
  have hstn := Restated.stamp_mono_sts facts S Sched x v (Nat.succ_le_of_lt hin) hst1
  have hclk : (x[i + 1][v].st).st.core.t < M.support_cutoff S.E s := by
    obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hstv
    rw [hstn] at hσ
    cases hσ
    exact WithBot.coe_lt_coe.mp hlt
  have hvc : v ∈ Sched.awake (M.support_cutoff S.E s) \
      Sched.adv (M.support_cutoff S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw (by rw [hsc]; linarith)
      (by rw [hsc, hct]; linarith), hvh _ (by rw [hsc, hct]; linarith)⟩
  have hti : (x[i + 1].time : Int) < M.support_cutoff S.E s :=
    Restated.time_lt_of_clock_lt facts S Sched x htd (facts.sch.support_cutoff_pos S s)
      (facts.sch.support_cutoff_emod_delta S s) hvc hclk
      (fun nc hnc => hneTickv nc _ hnc (facts.sch.support_cutoff_emod_delta S s) hvc
        (by rw [hsc]; linarith) (by rw [hsc, hct]; linarith))
  rw [hsc] at hti
  have hlo_i : slotStart S.E.Δ u.slot ≤ (x[i + 1].time : Int) :=
    Restated.slotStart_le_time_of_flip_gfVote facts S Sched x h0 h1
  rw [hus] at hlo_i
  have htsucc := Restated.time_succ_le facts S Sched x i
  have hii : (x[i].time : Int) ≤ (x[i + 1].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_succ i)
  have hvi : Restated.HonestThrough M Sched x i v := fun t ht => hvh t (by rw [hct]; linarith)
  have hawi : AtomicAwake x i w :=
    mem_awake_of_awakeThroughout Sched hwaw (by linarith) (by rw [hct]; linarith)
  have hwslot : w ∉ Sched.adv (slotStart S.E.Δ s) := hwh _ (by rw [hct]; linarith)
  have hmax : max (x[i + 1].time : Int) S.E.t_GST = (x[i + 1].time : Int) :=
    max_eq_left (by linarith)
  obtain ⟨k, -, hk1, hk⟩ :=
    Restated.gfVote_in_pool_of_accepts facts S Sched x (Restated.gfVoteRelayAtAccept_of_sync facts S Sched x hsync) htd h0 h1
      hvi hawi hcomm (by rw [hus]; exact hs) (by rw [hus]; exact hlo_i)
      (by rw [hus, hmax]; exact awakeThroughout_mono Sched hwaw (by linarith)
            (by rw [hct]; linarith))
      (by rw [hus]; exact hwslot)
      (by rw [hus, hmax, hss2]; linarith)
      (fun n' hn' => hneTickw n' _ hn' (slotStart_emod_delta S u.slot)
        (by rw [hus]; exact Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwaw (by linarith)
          (by rw [hct]; linarith), hwslot⟩)
        (by rw [hus]) (by rw [hus, hct]; linarith))
      (fun _ _ _ => facts.nd.process_nonempty _ _ _ (fun _ h => by cases h))
  rw [hmax] at hk1
  exact Restated.confLate_of_pool_at facts S Sched x (Restated.step_lt_of_time_lt facts S Sched x (by linarith)) hus
    (by rw [hct]; linarith) hk

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s` is positive and starts at or after GST, `n` is the tick step at its confirmation
    instant, `v` and `w` are awake from one delay before slot `s`'s start to that instant and honest
    through it, and the ticks named by `hneTickv` and `hneTickw` have an outcome, then the cross
    view holds between an outcome `votes` of `v`'s counted votes at slot `s` and `w`'s late view:
    each vote reaches that view or its signer is seen to equivocate there, and both stores' trees
    resolve each vote's head to the same block. -/
theorem confCrossView_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    {s : Slot} (hs : 0 < s) (hgsts : S.E.t_GST ≤ slotStart S.E.Δ s)
    {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    {v w : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hwaw : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hwh : HonestThroughTime Sched (M.confirmation_time S.E s) w)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out)
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes) :
    Restated.Vocabulary.Protocol.CrossView M (x[n][v].st).st.core.T (x[n][w].st).st.core.T
      votes
      (Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s) := by
  refine ⟨Restated.confVotes_transfer_confLate_afterPhase facts S Sched x hsync htd hs hgsts hn hvaw
    hvh hwaw hwh hneTickv hneTickw hvotes, ?_⟩
  intro u _ B C hB hC
  obtain ⟨-, hnself⟩ := Restated.tickStepAt_time facts x hn
  have hvn : Restated.HonestThrough M Sched x n v := fun t ht => hvh t (by linarith)
  have hwn : Restated.HonestThrough M Sched x n w := fun t ht => hwh t (by linarith)
  have hBT := Proofs.HealingLemmas.find?_mem hB
  have hCT := Proofs.HealingLemmas.find?_mem hC
  obtain ⟨Bn, hBn, hBne⟩ := Restated.exists_named_of_mem_tree facts S Sched x n v hBT
  obtain ⟨Cn, hCn, hCne⟩ := Restated.exists_named_of_mem_tree facts S Sched x n w hCT
  have hinj := Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hexec.idealization Bn Cn
    (Restated.blockInLog_of_mem_bodies facts S Sched hvn hBn) (Restated.blockInLog_of_mem_bodies facts S Sched hwn hCn)
  refine RootInjectiveOnAncestors.eq_of_root_eq hinj ?_ ?_
    ((Proofs.HealingLemmas.find?_root hB).trans (Proofs.HealingLemmas.find?_root hC).symm)
  · rw [hBne]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [hCne]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s` is positive and starts at or after GST, `n` is the tick step at its confirmation
    instant, `v` and `w` are awake from one delay before slot `s`'s start to that instant and honest
    through it, the ticks named by `hneTickv` and `hneTickw` have an outcome, an outcome `elv` of
    slot `s`'s eligibility test at `v`'s store after `n` steps passes `B`, and an outcome `elw` of
    it at `w`'s store passes `C`, then `B` and `C` lie on one chain. -/
theorem sameSlot_eligible_compatible_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x)
    {s : Slot} (hs : 0 < s) (hgsts : S.E.t_GST ≤ slotStart S.E.Δ s)
    {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    {v w : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hwaw : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hwh : HonestThroughTime Sched (M.confirmation_time S.E s) w)
    {B C : Block V}
    {elv elw : Block V → Bool}
    (helv : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][v].st).st.core s ⇢ elv)
    (hB : elv B = true)
    (helw : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][w].st).st.core s ⇢ elw)
    (hC : elw C = true)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    Block.compatible B C = true := by
  obtain ⟨votesv, hvv, hrv⟩ := (returns_bind_iff_cn _ _ _).1 helv
  obtain ⟨scv, hscv, hpv⟩ := (returns_bind_iff_cn _ _ _).1 hrv
  have hscv' := (returns_lift_iff_cn _ _).1 hscv
  rw [Record.returns_pure] at hpv
  subst hpv
  obtain ⟨votesw, hvw', hrw⟩ := (returns_bind_iff_cn _ _ _).1 helw
  obtain ⟨scw, hscw, hpw⟩ := (returns_bind_iff_cn _ _ _).1 hrw
  have hscw' := (returns_lift_iff_cn _ _).1 hscw
  rw [Record.returns_pure] at hpw
  subst hpw
  simp only [Restated.Vocabulary.Protocol.confCount, decide_eq_true_eq] at hB hC
  have hel : ∀ (st : M.S) (tm : TimestampMap (GoldfishVote V)), st.tau ⇢ tm →
      ∀ u ∈ beforeCutoff tm (M.support_cutoff S.E s) (M.store_pool st s),
        u ∈ Restated.Vocabulary.Protocol.confLate M S.E st s := by
    intro st tm htm u hu
    have h := (mem_beforeCutoff_iff _ _ _ _).mp hu
    refine (mem_beforeCutoff_iff _ _ _ _).mpr ⟨h.1, ?_⟩
    obtain ⟨σ, hσ, hlt⟩ :=
      exists_stamp_of_stampedBefore (facts.sto.stampedBefore_vote_of_tau st tm htm h.2)
    exact stampedBefore_of_lt hσ (lt_of_lt_of_le hlt
      (WithBot.coe_le_coe.mpr (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s)))
  have hvw := Restated.confCrossView_afterPhase facts S Sched x hexec hsync htd hs hgsts hn hvaw hvh
    hwaw hwh hneTickv hneTickw hvv
  have hwv := Restated.confCrossView_afterPhase facts S Sched x hexec hsync htd hs hgsts hn hwaw hwh
    hvaw hvh hneTickw hneTickv hvw'
  obtain ⟨ev, hev, rfl⟩ := returns_map_elim_cn _ _ _ hvv
  obtain ⟨tmv, htmv, rfl⟩ := returns_map_elim_cn _ _ _ hev
  obtain ⟨ew, hew, rfl⟩ := returns_map_elim_cn _ _ _ hvw'
  obtain ⟨tmw, htmw, rfl⟩ := returns_map_elim_cn _ _ _ hew
  exact facts.fc.eligible_compatible
    (fun u hu => hel _ tmv htmv u hu) rfl (fun u hu => hel _ tmw htmw u hu) rfl
    hvw.transfer hvw.resolve hwv.transfer hwv.resolve
    _ (hscv' B) hB _ (hscw' C) hC

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Stamping the clock of a store does not change its slot-`s` confirmation eligibility test. -/
private theorem confEligible_setClock_confNew (facts : Record.Facts M) (E : Env V) (st : M.NS)
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

/-- For every store `hs` the round-`r₁` action read can give from `before`, `hs`'s confirmed block
    passes every outcome of the eligibility test of `before`'s store for the slot before the action
    instant's slot, or is `confRoot` of `before`'s store with its clock set to the action instant. -/
private theorem actionHealingStore_live_confirmed_cases_confNew (facts : Record.Facts M)
    (S : Setup V) (before : M.N) (r₁ : Round) (hs : M.HS)
    (hhs : hs ∈ Restated.actionHealingStore M S before r₁) :
    (∀ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E before.st.core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) ⇢ el →
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
    intro el hel
    rw [← confEligible_setClock_confNew facts S.E before.st
      (Restated.Vocabulary.Execution.Setup.a M S r₁)] at hel
    obtain ⟨votes, hvv, hrv⟩ := (returns_bind_iff_cn _ _ _).1 hel
    obtain ⟨sc, hsc, hp⟩ := (returns_bind_iff_cn _ _ _).1 hrv
    have hsc' := (returns_lift_iff_cn _ _).1 hsc
    rw [Record.returns_pure] at hp
    subst hp
    obtain ⟨e, he, rfl⟩ := returns_map_elim_cn _ _ _ hvv
    obtain ⟨tm, htm, rfl⟩ := returns_map_elim_cn _ _ _ he
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing
      (M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.s)
    obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
      (M.get_filtered_block_tree
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing.toFG)
      sc
      (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * sc B))
    have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR sc hsc' W hW X hX
    have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR sc hsc' W hW X hX
    rcases hwalk with hwalk | hfg
    · rcases hgen with ⟨-, -, hgel⟩ | hfg
      · rw [hwalk]
        exact hgel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

/-- For every store and slot, the confirmation eligibility test has an outcome. -/
private theorem confEligible_nonempty_confNew (facts : Record.Facts M) (E : Env V) (st : M.S)
    (s : Slot) : ∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M E st s ⇢ el := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  have hvv : Restated.Vocabulary.Protocol.confVotes M E st s ⇢
      (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) :=
    returns_map_intro_cn _ _ _ (returns_map_intro_cn _ _ _ htm)
  obtain ⟨sc, hsc⟩ : ∃ sc : Block V → Nat, ∀ B, M.goldfish_score E st.T
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true))
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true))
      s B ⇢ sc B :=
    ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
      fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
  refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B), ?_⟩
  unfold Restated.Vocabulary.Protocol.confEligible
  refine (returns_bind_iff_cn _ _ _).2 ⟨_, hvv, ?_⟩
  refine (returns_bind_iff_cn _ _ _).2 ⟨sc, (returns_lift_iff_cn _ _).2 hsc, ?_⟩
  exact (Record.returns_pure _ _).2 rfl

/-- If `n'` is the tick step at `S.a (r + 1)` and `v` is in `HonRound S Sched (r + 1)`, then for
    every store `hs` `v`'s round-`(r + 1)` action read can give, either `hs`'s confirmed block
    passes every outcome of the eligibility test of `v`'s store after `n'` steps at round `r + 1`'s
    opening slot, or it is `confRoot` of that store stamped for the opening slot's confirmation
    (`confStoreAt`). -/
theorem live_confirmed_cases_honRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) :
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
    (∃ H : Block V,
      (∀ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E (x[n'][v].st).st.core
        ((M.opening_slot S.hc (r + 1))) ⇢ el → el H = true) ∧
      hs.live_confirmed = H) ∨
    hs.live_confirmed
      = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) := by
  intro hs hhs
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hcases := actionHealingStore_live_confirmed_cases_confNew facts S (x[n'][v].st) (r + 1) hs hhs
  rw [Restated.slotOf_a_sub_one facts S (r + 1)] at hcases
  rcases hcases with hel | hroot
  · exact Or.inl ⟨_, hel, rfl⟩
  · right
    rw [hroot, Restated.confStoreAt, hct]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `r + 1`'s opening slot starts at or after GST, `n'` is the tick step at `S.a (r + 1)`,
    `v` and `w` are in `HonRound S Sched (r + 1)`, `confRoot` of both validators' stores stamped for
    the opening slot's confirmation is an ancestor of `A`, `hsv` and `hsw` are stores of `v`'s and
    `w`'s round-`(r + 1)` action reads whose confirmed blocks each lie on one chain with `A`, and
    the ticks named by `hneTickv` and `hneTickw` have an outcome, then the two confirmed blocks lie
    on one chain. -/
theorem sameSlot_confirmed_compatible_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption)
    {r : Round} {n' : Nat}
    (hgsts : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v w : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) (hw : w ∈ Restated.HonRound M S Sched (r + 1))
    {A : Block V}
    (hrootv : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1))))) A)
    (hrootw : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n'][w].st) ((M.opening_slot S.hc (r + 1))))) A)
    (hsv : M.HS) (hhsv : hsv ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1))
    (hsw : M.HS) (hhsw : hsw ∈ Restated.actionHealingStore M S (x[n'][w].st) (r + 1))
    (hconfv : Block.compatible hsv.live_confirmed A = true)
    (hconfw : Block.compatible hsw.live_confirmed A = true)
    (hneTickv : ∀ (n'' : Nat) (t : Int), Restated.tickStepAt M x n'' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) ≤ t →
      t ≤ M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n''] v) t ⇢ out)
    (hneTickw : ∀ (n'' : Nat) (t : Int), Restated.tickStepAt M x n'' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) ≤ t →
      t ≤ M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n''] w) t ⇢ out) :
    Block.compatible hsv.live_confirmed hsw.live_confirmed = true := by
  rcases Restated.live_confirmed_cases_honRound facts S Sched x hn' hv hsv hhsv with
    ⟨Hv, hev, hlv⟩ | hlv
  · rcases Restated.live_confirmed_cases_honRound facts S Sched x hn' hw hsw hhsw with
      ⟨Hw, hew, hlw⟩ | hlw
    · have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        Restated.confirmation_time_opening_slot facts S (r + 1)
      have hn : Restated.tickStepAt M x n' (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
        rw [hct]; exact hn'
      have hvh : HonestThroughTime Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) v :=
        fun t ht hin => (Finset.mem_sdiff.1 hv).2 (hmono _ _ (le_of_le_of_eq ht hct) hin)
      have hwh : HonestThroughTime Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) w :=
        fun t ht hin => (Finset.mem_sdiff.1 hw).2 (hmono _ _ (le_of_le_of_eq ht hct) hin)
      rw [hlv, hlw]
      obtain ⟨elv, helv⟩ := confEligible_nonempty_confNew facts S.E (x[n'][v].st).st.core
        ((M.opening_slot S.hc (r + 1)))
      obtain ⟨elw, helw⟩ := confEligible_nonempty_confNew facts S.E (x[n'][w].st).st.core
        ((M.opening_slot S.hc (r + 1)))
      exact Restated.sameSlot_eligible_compatible_afterPhase facts S Sched x hexec hsync htd
        (facts.gr.opening_slot_pos S (Nat.succ_pos r)) hgsts hn
        (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv) hvh
        (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hw) hwh
        helv (hev elv helv) helw (hew elw helw) hneTickv hneTickw
    · rw [hlw]
      exact Protocol.compatible_comm
        (Protocol.compatible_of_preceq_of_compatible hrootw (Protocol.compatible_comm hconfv))
  · rw [hlv]
    rw [hlv] at hconfv
    exact Protocol.compatible_of_preceq_of_compatible hrootv (Protocol.compatible_comm hconfw)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T` and the conditions `hcross` and `hjust`:
    if `n'` is the tick step at `S.a (r + 1)` and `v` is in `HonRound S Sched (r + 1)`, then
    `confRoot` of `v`'s store after `n'` steps, stamped for round `r + 1`'s opening slot's
    confirmation, is an ancestor of `T`'s erasure. -/
theorem confRoot_preceq_anchor_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) :
    Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1))))) T.erase := by
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x
    tE hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← (Restated.tickStepAt_time facts x hn').1]; exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
    hvadv (hmono t _ (le_trans ht htn) hin)
  unfold Restated.Vocabulary.Protocol.confRoot Record.Model.S.toHealing
  refine facts.fc.fgRoot_preceq_ofJustifiedBranch ?_ ?_
  · rw [Restated.confStoreAt, facts.hd.setClock_toHealing_F]
    exact hfin v n' le_rfl hvn
  · intro hroot
    rw [Restated.confStoreAt, facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j] at hroot
    rw [Restated.confStoreAt, facts.hd.setClock_toHealing_J]
    exact Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x tE hexec
      hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' v n'
      (Restated.tick_succ_le_tick_succ_round facts S Sched x hinv.tick hn') le_rfl hvn hroot

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T`, the conditions `hcross` and `hjust`,
    `ConfirmedCompatibleFreshSGOverHonRound` and a choice `att` of the round-`(r + 1)` action
    attestations, and given that the ticks named by `hneTickVote`, `hneTickSlot`, `hneTick` and
    `hneAtt` have an outcome: the confirmed block of every store the round-`(r + 1)` action read of
    a member of `HonRound S Sched (r + 1)` can give lies on one chain with the round-`(r + 1)`
    anchor `newAnchor` read along `att`. -/
theorem confirmedNew_at_of_joint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
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
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n')
    (hneTickVote : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTickSlot : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.compatible hs.live_confirmed (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  classical
  intro v hv hs hhs
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hwin : ∀ v' ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t : Int),
      Restated.tickStepAt M x n'' t → t % S.E.Δ = 0 → v' ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) ≤ t →
      t ≤ M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v' (Record.wakeStage M Sched t x[n''] v') t ⇢ out :=
    fun v' hv' n'' t hn'' hΔ hq _ ht => hneTick v' hv' n'' t hn'' hΔ hq (by rw [← hct]; exact ht)
  have hold : ∀ v' ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs' ∈ Restated.actionHealingStore M S (x[n'][v'].st) (r + 1),
      Block.compatible hs'.live_confirmed T.erase = true :=
    fun v' hv' => Restated.confirmedOld_at_honRound (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust) S Sched x
      tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hv'
      hneTickVote hneTickSlot (hneTick v' hv') hneAtt
  have hroot : ∀ v' ∈ Restated.HonRound M S Sched (r + 1), Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n'][v'].st) ((M.opening_slot S.hc (r + 1))))) T.erase :=
    fun v' hv' => Restated.confRoot_preceq_anchor_of_premises facts (hcross := hcross) (hjust := hjust) S Sched x
      tE hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' hv'
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    have hqH : q ∈ Restated.HonRound M S Sched (r + 1) :=
      Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hqW
    obtain ⟨nq, hnq, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := actionFGSource_nonempty_cn facts (Setup.alwaysAwake S) nq
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl nq hnq (ns, rec, att q) hD
        hvote _ ho
    have hqs : M.toHealing nq.st.core ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1) :=
      ⟨nq, hnq, rfl⟩
    rw [hchoice]
    rcases Restated.source_cases facts S (x[n'][q].st) (r + 1) nq hnq Cfg ho with hlc | hQ2
    ·
      have hgsts : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by
        have h1 := Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen
        unfold Restated.switchOpening at h1
        rw [facts.gr.opening_eq_proposal_time] at h1
        have h2 := facts.sch.proposal_time_le_confirmation_time S.E
          (M.opening_slot S.hc (Restated.switchRound M S tE))
        have h3 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
          (M.opening_slot S.hc (Restated.switchRound M S tE))
        have hos : M.opening_slot S.hc (Restated.switchRound M S tE) + 1 + 1
            ≤ M.opening_slot S.hc (r + 1) := by
          have ha := facts.gr.opening_slot_mono S hr
          have hR : 2 ≤ S.hc.R := by have := S.hc.R_ge_three; omega
          rw [facts.gr.opening_slot_succ S.hc r]
          calc _ ≤ M.opening_slot S.hc r + 2 := Nat.add_le_add_right ha 2
            _ ≤ _ := Nat.add_le_add_left hR _
        have h4 := slotStart_le_slotStart (le_of_lt S.E.Δ_pos) hos
        have h5 := slotStart_succ S.E.Δ (M.opening_slot S.hc (Restated.switchRound M S tE))
        have h6 := slotStart_succ S.E.Δ (M.opening_slot S.hc (Restated.switchRound M S tE) + 1)
        have hd := S.E.Δ_pos
        linarith
      have hsame := Restated.sameSlot_confirmed_compatible_afterPhase facts S Sched x hexec hsync htd
        hmono hgsts hn' hv hqH (hroot v hv) (hroot q hqH) hs hhs _ hqs (hold v hv hs hhs)
        (hold q hqH _ hqs) (hwin v hv) (hwin q hqH)
      exact compatible_of_preceq_of_preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
        (preceq_trans_Preceq hpre hlc) hsame
    ·
      obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nq.cache) S.E S.hc
        (M.toHealing nq.st.core) (r + 1)
      have hgQ : g.Q2 = some Cfg := hQ2 g ((facts.nd.gradeContract_read _ _ _ _ _ _).1 hg)
      obtain ⟨o₂, ho₂⟩ := facts.gr.grade2Block_nonempty (M.toHealing nq.st.core)
        (M.readFrame nq.cache (M.toHealing nq.st.core) (r + 1))
      have hgo : g.Q2 = o₂ :=
        facts.nd.ModelProperties_gradeContract_read_Q2 nq.cache S.E S.hc (M.toHealing nq.st.core)
          (r + 1) g hg o₂ ho₂
      obtain ⟨root, hroot2, hQroot⟩ := facts.gr.grade2Block_preceq_root o₂ ho₂ (by rw [← hgo, hgQ])
      obtain ⟨m₂, G, hm₂, hG, hrootG⟩ :=
        Restated.actionFrame_g2_provenance facts S Sched x hn' q root _ ⟨nq, hnq, rfl⟩ hroot2
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m₂][q].st).st.core))
        (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
        (M.late S.E S.hc (r + 1) .g2) G
      have hbt := hG b hb
      subst hbt
      obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hGC⟩ :=
        Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono
          htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hqH
          (facts.gr.domain_le_action S (r + 1) .g2) hm₂ G hb hneTick hneAtt
      exact compatible_of_preceq_of_preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
        (preceq_trans_Preceq hpre (preceq_trans_Preceq hQroot (preceq_trans_Preceq hrootG hGC)))
        (Protocol.compatible_comm (hQ v hv v_1 hv_1 a har hai has C hC hac hs hhs))
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = T := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = T
      rw [dif_neg hex]
    rw [hchoice]
    exact hold v hv hs hhs

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T` and the condition `hcross`: if the
    justified block of every store of the round-`(r + 1)` action read of a validator honest through
    `S.a (r + 1)` is an ancestor of `T`, the confirmed block of every such store of a member of
    `HonRound S Sched (r + 1)` lies on one chain with `T`, `ConfirmedCompatibleFreshSGOverHonRound`
    holds, and the ticks named by `hneTick` and `hneAtt` have an outcome, then `GradePairwise` holds
    for any two members of `HonRound S Sched (r + 1)`, any node states of their round-`(r + 1)`
    action reads and any grade reads of their frames. -/
theorem gradePairwise_ofConfirmedCompatibleFreshSGOverHonRound_honRound (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
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
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hJ : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1), Block.Preceq hs.J T.erase)
    (hconf : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
        Block.compatible hs.live_confirmed T.erase = true)
    (hconfSG : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n')
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
    ∀ m₁ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₁].st) (r + 1),
    ∀ m₂ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₂].st) (r + 1),
    ∀ g₁, M.frameGradeRead m₁.cache S.E S.hc (M.toHealing m₁.st.core) (r + 1) ⇢ g₁ →
    ∀ g₂, M.frameGradeRead m₂.cache S.E S.hc (M.toHealing m₂.st.core) (r + 1) ⇢ g₂ →
      Restated.GradePairwise M (M.toHealing m₁.st.core) (M.toHealing m₂.st.core) g₁ g₂ := by
  intro v₁ hv₁ v₂ hv₂ m₁ hm₁ m₂ hm₂ g₁ hg₁ g₂ hg₂ B₁ B₂ hc₁ hc₂ hgr
  have hkind : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v].st) (r + 1),
      ∀ g, M.frameGradeRead m.cache S.E S.hc (M.toHealing m.st.core) (r + 1) ⇢ g →
      ∀ B : Block V, SGGraded g B →
      Restated.PreceqFreshSG M S Sched x r n B ∨ Block.Preceq B T.erase := fun v hv m hm g hg B hB =>
    Restated.sgGraded_preceqFreshSG_or_preceq_anchor (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono
      htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hJ hv hm hg hB hneTick
      hneAtt
  have hany : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v].st) (r + 1),
      ∀ g, M.frameGradeRead m.cache S.E S.hc (M.toHealing m.st.core) (r + 1) ⇢ g →
      ∀ B : Block V, Restated.SGCandidate M (M.toHealing m.st.core) g B →
      Restated.PreceqFreshSG M S Sched x r n B ∨ Block.Preceq B T.erase ∨
        Block.Preceq B (M.toHealing m.st.core).live_confirmed := by
    intro v hv m hm g hg B hB
    rcases hB with hL | hG
    · exact Or.inr (Or.inr hL)
    · rcases hkind v hv m hm g hg B hG with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hSGat : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v].st) (r + 1),
      ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V, a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase (M.toHealing m.st.core).live_confirmed = true :=
    fun v hv m hm v_1 hv_1 a h1 h2 h3 C hC hc =>
      hconfSG v hv v_1 hv_1 a h1 h2 h3 C hC hc _ ⟨m, hm, rfl⟩
  rcases hgr with hgr₁ | hgr₂
  · exact Restated.compatible_of_kinds facts S Sched x hinv (hconf v₂ hv₂ _ ⟨m₂, hm₂, rfl⟩)
      (hSGat v₂ hv₂ m₂ hm₂) (hkind v₁ hv₁ m₁ hm₁ g₁ hg₁ B₁ hgr₁) (hany v₂ hv₂ m₂ hm₂ g₂ hg₂ B₂ hc₂)
  · exact Protocol.compatible_comm (Restated.compatible_of_kinds facts S Sched x hinv
      (hconf v₁ hv₁ _ ⟨m₁, hm₁, rfl⟩) (hSGat v₁ hv₁ m₁ hm₁) (hkind v₂ hv₂ m₂ hm₂ g₂ hg₂ B₂ hgr₂)
      (hany v₁ hv₁ m₁ hm₁ g₁ hg₁ B₁ hc₁))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T`, the conditions `hcross`, `hjust` and
    `hJ`, and `ConfirmedCompatibleFreshSGOverHonRound`, and given that the ticks named by
    `hneTickVote`, `hneTickSlot`, `hneTick` and `hneAtt` have an outcome: `GradePairwise` holds for
    any two members of `HonRound S Sched (r + 1)`, any node states of their round-`(r + 1)` action
    reads and any grade reads of their frames. -/
theorem gradePairwise_at_of_confirmedSafe (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
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
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hJ : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1), Block.Preceq hs.J T.erase)
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n')
    (hneTickVote : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTickSlot : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
    ∀ m₁ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₁].st) (r + 1),
    ∀ m₂ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₂].st) (r + 1),
    ∀ g₁, M.frameGradeRead m₁.cache S.E S.hc (M.toHealing m₁.st.core) (r + 1) ⇢ g₁ →
    ∀ g₂, M.frameGradeRead m₂.cache S.E S.hc (M.toHealing m₂.st.core) (r + 1) ⇢ g₂ →
      Restated.GradePairwise M (M.toHealing m₁.st.core) (M.toHealing m₂.st.core) g₁ g₂ :=
  Restated.gradePairwise_ofConfirmedCompatibleFreshSGOverHonRound_honRound (hrecvR := hrecvR) facts (hcross := hcross) S Sched
    x tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hJ
    (fun _ hv => Restated.confirmedOld_at_honRound (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust) S Sched x
      tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hv
      hneTickVote hneTickSlot (hneTick _ hv) hneAtt)
    hQ hneTick hneAtt

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T`, the condition `hcross`, a choice `att`
    of the round-`(r + 1)` action attestations and `ConfirmedCompatibleFreshSGOverHonRound`, and
    given that the ticks named by `hneTick` and `hneAtt` have an outcome: every block a member of
    `HonRound S Sched (r + 1)` can grade at least 1 for round `r + 1`, at a phase whose domain
    instant is at or before `S.a (r + 1)`, and that has `T` as a strict ancestor, lies on one chain
    with the round-`(r + 1)` anchor read along `att`. -/
theorem gradeDescendant_at_of_confirmedSafe (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n')
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
    ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.Preceq T.erase B → B ≠ T.erase →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true :=
  Restated.gradeDescendant_ofConfirmedFreshSG (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono htd
    hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hatt
    (Restated.confirmedCompatibleFreshSG_of_overHonRound facts S Sched x hn' hQ) hneTick hneAtt

end

end DecoupledConsensusModel.Sts.Restated
