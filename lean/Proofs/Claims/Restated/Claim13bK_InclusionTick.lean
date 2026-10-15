import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeHeads
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_ConfirmedAgree
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedWake
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# The confirmed output after a confirmation tick

Under a cone of support the confirmation walk's result passes the eligibility test, and right after
the tick at a confirmation instant the confirmed output of an honest awake reader is a descendant of
every block the honest heads descend from. Stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
open DecoupledConsensusModel.Execution

/-- For `0 < s`, `support_cutoff s = slotStart s + 2Δ`. -/
private theorem support_cutoff_eq_of_pos (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

/-- Along one path of the confirmation walk from `A`: if the counted votes `e` carry a cone of
    support for the descendants of `B` over an honest set, every vote of the store's late view is of
    slot `s` and by a member of its committee, `A` is an ancestor of `B`, and every block from `A`
    (excluded) to `B` is in the walk's tree, then `B` is an ancestor of the walk's result `W`, and
    the count of the late view is less than twice `sc W`. -/
private theorem confWalkWith_eligible_of_cone (facts : Record.Facts M)
    (E : Env V) (st : M.S) (s : Slot) (Hon : Finset V) {B : Block V} (A : Block V)
    (e : Finset (GoldfishVote V)) (sc : Block V → ℕ)
    (hsc : ∀ C, M.goldfish_score E st.T e e s C ⇢ sc C)
    (hsup : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M E st.T e e
      (Restated.Vocabulary.Protocol.confLate M E st s) s Hon (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E s (Restated.Vocabulary.Protocol.confLate M E st s))
    (hpre : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
      C ∈ Restated.Vocabulary.Protocol.confTree M st)
    (W : Block V)
    (hW : M.ghost A (Restated.Vocabulary.Protocol.confTree M st) sc
      (fun C => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc C)) ⇢ W) :
    Block.Preceq B W ∧
      decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc W) = true := by
  have hwalk : Block.Preceq B W :=
    facts.fc.ghost_passes_cone E st.T (Restated.Vocabulary.Protocol.confTree M st) e e
      (Restated.Vocabulary.Protocol.confLate M E st s) s Hon hsup.majority hsup.counted hsup.sub
      hsup.no_equiv hsup.vote hvalid hpre hpath sc hsc W hW
  refine ⟨hwalk, ?_⟩
  rcases facts.fc.ghost_eligible A (Restated.Vocabulary.Protocol.confTree M st) sc
      (fun C => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc C)) W hW with hA | hel
  · have hAB : A = B := Proofs.ModelProperties.Preceq_antisymm hpre (hA ▸ hwalk)
    rw [hA, hAB]
    simp only [decide_eq_true_eq, Restated.Vocabulary.Protocol.confCount]
    exact facts.fc.ConeSupport_eligible E st.T e e (Restated.Vocabulary.Protocol.confLate M E st s)
      s Hon (fun X => Block.Preceq B X) hsup.majority hsup.counted hsup.sub hsup.no_equiv
      hsup.vote hvalid (fun X hX => preceq_eq_true_iff_Preceq.mpr hX) (sc B) (hsc B)
  · exact hel

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_it {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_it {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- At every store `st` some block is an outcome of `gfHeadWith`. -/
private theorem gfHeadWith_nonempty_it (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.S) :
    ∃ H, Restated.gfHeadWith M contract E hc st ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty E st st.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨U, hU⟩ :=
    facts.fc.voter_support_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty contract E hc (M.toHealing st)
    T W U (st.s - 1)
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadWith
  exact (returns_bind_iff_it _ _ _).2 ⟨T, hT, (returns_bind_iff_it _ _ _).2
    ⟨W, hW, (returns_bind_iff_it _ _ _).2 ⟨U, hU,
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH⟩⟩⟩

/-- From every node state `before`, some block is an outcome of `gfHeadFrom` at slot `s`. -/
private theorem gfHeadFrom_nonempty_it (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) : ∃ H, Restated.gfHeadFrom M S before s ⇢ H := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_it _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty_it facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_it _ _ _).2 ⟨_, hn, hH⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s` is positive and starts at or after `tGAT`, the committee majority holds from `tE`,
    the delivery condition at `B` holds up to `tR`, every honest active member of slot `s`'s
    committee votes for a descendant of `B`, `v` is awake from one delay before slot `s`'s start to
    its confirmation instant and honest through it, the ticks of `hneTickVote` and `hneTick` have
    outcomes, and an outcome `A` of the walk's start is an ancestor of `B` with every block from `A`
    (excluded) to `B` in the walk's tree, then along every path of the walk from `A`, `B` is an
    ancestor of the result `W` and the count of the late view is less than twice `sc W`. -/
theorem walk_eligible_of_headsBelow_at_confirmation_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR B)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR B)
    {s : Slot} (hs : 0 < s) (hslo : tGAT ≤ slotStart S.E.Δ s)
    (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hsR : M.support_cutoff S.E s ≤ tR)
    (hprev : Restated.HeadsBelow M S Sched x B s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (contract : M.Contract)
    (A : Block V)
    (hA : Restated.Vocabulary.Protocol.confAnchorWith M contract S.E S.hc
      (Restated.confStoreAt M S (x[m][v].st) s) ⇢ A)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A →
      Block.Preceq C B → C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s))
    (hneTickVote : ∀ mv : Nat, Restated.tickStepAt M x mv (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[mv] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t' ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[m][v].st) s) s ⇢ e →
    ∀ sc : Block V → ℕ, (∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[m][v].st) s).T
        e e s C ⇢ sc C) →
    ∀ W, M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s))
        sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (Restated.confStoreAt M S (x[m][v].st) s) s < 2 * sc C)) ⇢ W →
      Block.Preceq B W ∧
        decide (Restated.Vocabulary.Protocol.confCount M S.E
          (Restated.confStoreAt M S (x[m][v].st) s) s < 2 * sc W) = true := by
  intro e he sc hscore W hW
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨-, hmself⟩ := Restated.tickStepAt_time facts x hm
  have hmrlo : M.support_cutoff S.E s ≤ (x[m].time : Int) := by
    rw [hsc]; rw [hct] at hmself; linarith
  have hmrc : (x[m].time : Int) ≤ M.confirmation_time S.E s := by
    rw [hct]; rw [hct] at hmself; linarith
  have hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s) :=
    awakeThroughout_mono Sched hvaw (by linarith) (by rw [hsc, hct]; linarith)
  have hw : v ∉ Sched.adv (x[m].time : Int) := hvh _ hmrc
  have hwh : v ∉ Sched.adv (slotStart S.E.Δ s) := hvh _ (by rw [hct]; linarith)
  obtain ⟨mv, hmv⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hs)
  have hheads := Restated.coneHeads_afterPhase facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird
    hcs hlen hunder hunderS hprev hmv hmrlo hslo hsR hw hwaw
    (fun n' t' h1 hΔ hq h2 => hneTick n' t' h1 hΔ hq (le_trans h2 hmrc))
  have hcone := Restated.coneSupport_at_confirmation facts S Sched x hexec hsync htd hmono hcs hs hanchor
    (le_trans hgst hslo) hmv hmrlo hmrc hwaw hwh
    (fun q hq => by
      obtain ⟨H, hH⟩ := gfHeadFrom_nonempty_it facts S (x[mv][q].st) s
      exact ⟨H, hH, hheads q hq H hH⟩)
    (hneTickVote mv hmv)
    (fun n hn => hneTick n _ hn (slotStart_emod_delta S s)
      (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwaw le_rfl (by rw [hsc]; linarith), hwh⟩)
      (by rw [hct]; linarith)) e he
  exact confWalkWith_eligible_of_cone facts S.E (Restated.confStoreAt M S (x[m][v].st) s) s
    (Restated.HonSlot M S Sched s) A e sc hscore hcone (Restated.voteSetValid_conf facts S Sched x m v s)
    hAB hpath W hW

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the committee majority `committeeSleepinessW` from `tE`, if a store's `latest_stable`, its
    `F` and its `latest_confirmed` are each an ancestor of every honest head from some slot on, and
    `X` is an ancestor of the store's `latest_confirmed`, then `X` is an ancestor of `get_confirmed`
    of the store. -/
theorem preceq_get_confirmed_of_records (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) (st : M.S) {s_0 s_1 s_2 : Slot}
    (hL : Restated.AncestorOfHonestHeadsFrom M S Sched x st.latest_stable s_0)
    (hF : Restated.AncestorOfHonestHeadsFrom M S Sched x st.F s_1)
    (hC : Restated.AncestorOfHonestHeadsFrom M S Sched x st.latest_confirmed s_2)
    {X : Block V} (hX : Block.Preceq X st.latest_confirmed) :
    Block.Preceq X (M.get_confirmed st) := by
  have hS : Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_stable st) (s_0 + s_1) :=
    Restated.ancestorOfHonestHeadsFrom_get_stable facts S Sched x st
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right s_0 s_1) hL)
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_left s_1 s_0) hF)
  have hcomp := Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hS hC
  exact preceq_trans_Preceq hX (facts.hd.get_confirmed_upper st hcomp).2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the committee majority `committeeSleepinessW` from `tE`, if along one path of `v`'s
    confirmation walk at slot `s`'s confirmation instant the result `W` passes the eligibility test,
    `X` is an ancestor of `W`, and `W`, `v`'s `latest_confirmed` after `m` steps, and `v`'s
    `latest_stable` and `F` after `m + 1` steps are each an ancestor of every honest head from some
    slot on, and `v`'s tick there has an outcome (`hneTick`), then `X` is an ancestor of `v`'s
    confirmed output after `m + 1` steps. -/
theorem preceq_get_confirmed_after_confirmation_tick_of_inputs (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) 
    (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) {s : Slot}
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
      (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (A : Block V) (hAo : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[m][v].st) s) ⇢ A)
    (e : Finset (GoldfishVote V))
    (he : Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[m][v].st) s) s ⇢ e)
    (sc : Block V → ℕ)
    (hsc : ∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[m][v].st) s).T e e s C ⇢ sc C)
    (W : Block V)
    (hWg : M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s))
      sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (Restated.confStoreAt M S (x[m][v].st) s) s < 2 * sc C)) ⇢ W)
    (hel : decide (Restated.Vocabulary.Protocol.confCount M S.E
      (Restated.confStoreAt M S (x[m][v].st) s) s < 2 * sc W) = true)
    {X : Block V} (hXW : Block.Preceq X W)
    {s_0 s_1 s_2 s_3 : Slot}
    (hW : Restated.AncestorOfHonestHeadsFrom M S Sched x W s_0)
    (hold : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_confirmed s_1)
    (hL : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_stable s_2)
    (hF : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.F s_3)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.confirmation_time S.E s) ⇢ out)
    -- `hrun`: the node state `v`'s tick reads passes the grade-2 awake test of the round of
    -- `s + 1`.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    Block.Preceq X (M.get_confirmed (x[m + 1][v].st).st.core) := by
  set stc := Restated.confStoreAt M S (x[m][v].st) s with hstc
  have hstc' : stc = (M.ns_setClock S.E (x[m][v].st).st
      (M.confirmation_time S.E s)).core := rfl
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc stc s
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc (M.toHealing stc)
    (M.round_of S.hc stc.s)
  have ho : (M.gradeContract c).stableRoot S.E S.hc (M.toHealing stc) (M.round_of S.hc stc.s) ⇢ o :=
    (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).2 ho'
  obtain ⟨G, hG, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x hm haw
    hneTick hrun c hc o ho
  have hupdstab : D.latest_stable = (x[m + 1][v].st).st.core.latest_stable := by
    rw [facts.hd.update_confirmation_with_latest_stable_of_root (M.gradeContract c) S.E S.hc stc s
      o ho hG D hD, hstab, hstc', facts.hd.setClock_core_latest_stable]
  have hold' : stc.latest_confirmed = (x[m][v].st).st.core.latest_confirmed := by
    rw [hstc', facts.hd.setClock_core_latest_confirmed]
  obtain ⟨e0, he0, rfl⟩ := (pCW% returns_map_elim_cw) _ _ _ he
  obtain ⟨tm, htm, rfl⟩ := (pCW% returns_map_elim_cw) _ _ _ he0
  have hrec : (x[m + 1][v].st).st.core.latest_confirmed
      = M.floor_on_stable (x[m + 1][v].st).st.core.latest_stable
          (M.advance_confirmed (x[m][v].st).st.core.latest_confirmed W)
          (x[m][v].st).st.core.latest_confirmed := by
    rw [hconf D hD, facts.hd.update_confirmation_with_latest_confirmed_of_eligible (M.gradeContract c) S.E S.hc stc s tm htm A hAo sc hsc W hWg hel
      D hD, hupdstab, hold']
  have hcand : Restated.AncestorOfHonestHeadsFrom M S Sched x
      (M.advance_confirmed (x[m][v].st).st.core.latest_confirmed W) (s_0 + s_1) :=
    Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right s_0 s_1) hW)
      (fun _ => Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_left s_1 s_0) hold)
  have hcomp := Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hL hcand
  have hXC : Block.Preceq X (x[m + 1][v].st).st.core.latest_confirmed := by
    rw [hrec]
    exact facts.hd.preceq_floor_on_stable_of_compatible _ hcomp
      (preceq_trans_Preceq hXW (facts.hd.preceq_advance_confirmed_candidate _ W))
  have hC : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_confirmed
      (s_2 + (s_0 + s_1)) := by
    rw [hrec]
    exact Restated.ancestorOfHonestHeadsFrom_floor_on_stable facts S Sched x
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right s_2 _) hL)
      (fun _ => Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_left _ s_2) hcand)
      (fun _ => Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x
        (le_trans (Nat.le_add_left s_1 s_0) (Nat.le_add_left _ s_2)) hold)
  exact Restated.preceq_get_confirmed_of_records facts S Sched x htd hcs _ hL hF hC hXC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `afterPhaseJointRound_of_premises` and `RecordsSettledAtSettleTick`, if every
    honest active committee member of every slot from `s` on votes for a descendant of `X`, the
    delivery condition at `X` holds up to slot `s`'s support cutoff, `v` is awake from one delay
    before slot `s`'s start to its confirmation instant and honest through the step after the tick
    there, and for an outcome `A` of the start of `v`'s confirmation walk the honest heads of slot
    `s` descend from `A` and the blocks from `A` (excluded) to `X` are in the walk's tree, then
    right after that tick `v`'s confirmed output is a descendant of `X`. -/
theorem get_confirmed_descendant_after_confirmation_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s)
    {X : Block V} (hX : Restated.AncestorOfHonestHeadsFrom M S Sched x X s)
    (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT
      (M.support_cutoff S.E s) X)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT (M.support_cutoff S.E s) X)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V} (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : Restated.HonestThrough M Sched x (m + 1) v)
    -- `hrun`: the node state `v`'s tick reads passes the grade-2 awake test of the round of
    -- `s + 1`.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
      (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (A : Block V) (hAo : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[m][v].st) s) ⇢ A)
    (hA : Restated.HeadsBelow M S Sched x A s)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A →
      Block.Preceq C X → C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s)) :
    Block.Preceq X (M.get_confirmed (x[m + 1][v].st).st.core) := by
  have hd := S.E.Δ_pos
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have hvh' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
    fun t ht => hvh t (by rw [hm1]; exact ht)
  have hawtc : v ∈ Sched.awake (M.confirmation_time S.E s) :=
    mem_awake_of_awakeThroughout Sched hvaw (by rw [hct]; linarith) le_rfl
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s) :=
    Finset.mem_sdiff.2 ⟨hawtc, hvh' _ le_rfl⟩
  have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x
    hexec.idealization.root_injective hexec.honestRootsNew hmono hm hdvd haw
  have hop : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) :=
    facts.gr.opening_slot_mono S (Nat.le_succ _)
  have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s :=
    le_trans (Nat.add_le_add_right hop 2) hslot
  have hspos : 0 < s :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 2) (le_trans (Nat.le_add_left 2 _) hslot)
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ := Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap
    hgst hlen hphase hcs (r := Restated.switchRound M S tE + 1) (Nat.le_succ _)
  have hanchor : t' ≤ slotStart S.E.Δ (s + 1) :=
    le_trans ht's (slotStart_mono S (le_trans hslot (Nat.le_succ s)))
  have hslo : tGAT ≤ slotStart S.E.Δ s := by
    have h1 := Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen
    have h2 := Restated.switchOpening_le_opening facts S (tE := tE) (r := Restated.switchRound M S tE) le_rfl
    rw [(pHP% opening_eq_slotStart_hp) facts] at h2
    have h6 := slotStart_mono S (le_trans (Nat.le_add_right _ 2) hs0)
    linarith
  have hawake' : ∀ t : Int, tGAT ≤ t → t ≤ t' → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h0 h1 => hphase t h0 (le_trans h1 ht'E)
  have hthird' : ∀ t : Int, t ≤ t' →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t h1 => hthird t (le_trans h1 ht'E)
  -- step 1: `A` and `X` lie on one chain
  have hAX : Block.compatible A X = true :=
    Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hspos hanchor hA (hX s le_rfl)
  -- step 2: one path of the walk; its result is a descendant of `X` and passes the test
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty (Restated.confStoreAt M S (x[m][v].st) s)
  have he : Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[m][v].st) s) s ⇢
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s)
          ((Restated.confStoreAt M S (x[m][v].st) s).pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff (Restated.confStoreAt M S (x[m][v].st) s).timestamp_vote
            (M.confirmation_time S.E s) ((Restated.confStoreAt M S (x[m][v].st) s).pool s)) u = true)) :=
    (pCW% returns_map_intro_cw) _ _ _ ((pCW% returns_map_intro_cw) _ _ _ htm)
  have hscore : ∀ C : Block V, ∃ g, M.goldfish_score S.E (Restated.confStoreAt M S (x[m][v].st) s).T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s)
          ((Restated.confStoreAt M S (x[m][v].st) s).pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff (Restated.confStoreAt M S (x[m][v].st) s).timestamp_vote
            (M.confirmation_time S.E s) ((Restated.confStoreAt M S (x[m][v].st) s).pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s)
          ((Restated.confStoreAt M S (x[m][v].st) s).pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff (Restated.confStoreAt M S (x[m][v].st) s).timestamp_vote
            (M.confirmation_time S.E s) ((Restated.confStoreAt M S (x[m][v].st) s).pool s)) u = true))
      s C ⇢ g :=
    fun C => facts.fc.goldfish_score_nonempty _ _ _ _ _ _
  choose sc hsc using hscore
  obtain ⟨W, hWg⟩ := facts.fc.ghost_nonempty A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s)) sc
    (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E (Restated.confStoreAt M S (x[m][v].st) s) s < 2 * sc C))
  have hwalk : Block.Preceq X W ∧
      decide (Restated.Vocabulary.Protocol.confCount M S.E (Restated.confStoreAt M S (x[m][v].st) s) s < 2 * sc W) = true := by
    rcases compatible_cases hAX with hAXp | hXA
    · exact Restated.walk_eligible_of_headsBelow_at_confirmation_tick facts S Sched x hexec hsync hmult
        htd hmono hgst hcv hawake' hthird' hcs' ht'len hunder
        hunderS hspos hslo hanchor le_rfl (hX s le_rfl) hm
        hvaw hvh' (M.gradeContract c) A hAo hAXp hpath
        (by intro mv hmv q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hmv (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) _ he sc hsc W hWg
    · have hunderA : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT
          (M.support_cutoff S.E s) A := Restated.deliveredDescendant_mono facts S Sched x hunder hXA
      have hunderAS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT
          (M.support_cutoff S.E s) A := Restated.finalizedPreceqAtSteps_mono facts S Sched x hunderS hXA
      have hpathA : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C A →
          C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s) :=
        fun C h1 h2 h3 => absurd (Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr h3)
          (preceq_eq_true_iff_Preceq.mpr h1)) h2
      obtain ⟨h1, h2⟩ := Restated.walk_eligible_of_headsBelow_at_confirmation_tick facts S Sched x hexec
        hsync hmult htd hmono hgst hcv hawake' hthird' hcs' ht'len hunderA
        hunderAS hspos hslo hanchor le_rfl hA
        hm hvaw hvh' (M.gradeContract c) A hAo (preceq_eq_true_iff_Preceq.mp (Block.preceq_self A)) hpathA
        (by intro mv hmv q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hmv (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) _ he sc hsc W hWg
      exact ⟨preceq_trans_Preceq hXA h1, h2⟩
  obtain ⟨hXW, hel⟩ := hwalk
  -- step 3: the walk's result is the `live_confirmed` the tick writes
  have hJ1 := Restated.live_confirmed_ancestorOfHonestHeadsFrom_ofJoint facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
    hAW hJswitch le_rfl hTW₀ hJ₀ hs0 hm hvaw hvh' hrun
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (Restated.confStoreAt M S (x[m][v].st) s) s
  have hlive := (pW% live_confirmed_after_confirmation_tick_outcome_csw) facts S Sched x hm haw
    hneTick hrun c hc D hD
  have hDW := facts.hd.update_confirmation_with_live_confirmed_of_eligible (M.gradeContract c) S.E S.hc
    (Restated.confStoreAt M S (x[m][v].st) s) s tm htm A hAo sc hsc W hWg hel D hD
  rw [hlive, hDW] at hJ1
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  have hsa : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1))
      = slotStart S.E.Δ ((M.opening_slot S.hc (Restated.switchRound M S tE + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (Restated.switchRound M S tE + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hlt : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) < (x[m].time : Int) := by
    have := slotStart_mono S hslot
    have e : slotStart S.E.Δ ((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2)
        = slotStart S.E.Δ ((M.opening_slot S.hc (Restated.switchRound M S tE + 1))) + 8 * S.E.Δ := by
      have h := slotStart_add S.E.Δ ((M.opening_slot S.hc (Restated.switchRound M S tE + 1))) 2
      push_cast at h
      linarith
    have hd1 : (1 : Int) ≤ S.E.Δ := hd
    rw [hct] at hm0
    linarith
  have hkm : n_b + 1 ≤ m := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  have hvm : Restated.HonestThrough M Sched x m v :=
    fun t ht => hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ m)))
  have hrecm := Restated.records_ancestorOfHonestHeads_after_settleTick facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
    hAW hJswitch hTW₀ hJ₀ hsettle hn_b v m hkm hvm
  have hrecm1 := Restated.records_ancestorOfHonestHeads_after_settleTick facts S Sched x tE hexec hmono htd
    hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear
    hB' hnW hAW hJswitch hTW₀ hJ₀ hsettle hn_b v (m + 1) (Nat.le_succ_of_le hkm) hvh
  have hk1 : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[m + 1].time : Int) := by
    have := Restated.action_mono facts S (Nat.le_succ (Restated.switchRound M S tE))
    have := Restated.time_mono_int facts S Sched x (Nat.le_succ m)
    linarith
  have hF := Restated.finalized_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
    le_rfl hTW₀ hJ₀ hk1 hvh
  -- steps 4 and 5
  exact Restated.preceq_get_confirmed_after_confirmation_tick_of_inputs facts S Sched x htd hcs hm haw
    c hc A hAo _ he sc hsc W hWg hel hXW hJ1 hrecm.2 hrecm1.1 hF hneTick hrun

end

end DecoupledConsensusModel.Sts.Restated
