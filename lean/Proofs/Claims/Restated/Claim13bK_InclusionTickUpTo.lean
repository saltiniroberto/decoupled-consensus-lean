import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeHeadsUpTo
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bStepConeUpTo
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# The confirmation walk under a cone of support, with synchrony up to a bound

The confirmation walk's result passes the eligibility test under a cone of support, with synchrony
assumed only up to slot `s`'s support cutoff, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

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
private theorem returns_map_intro_itu {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_itu {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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
private theorem gfHeadWith_nonempty_itu (facts : Record.Facts M) (contract : M.Contract)
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
  exact (returns_bind_iff_itu _ _ _).2 ⟨T, hT, (returns_bind_iff_itu _ _ _).2
    ⟨W, hW, (returns_bind_iff_itu _ _ _).2 ⟨U, hU,
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH⟩⟩⟩

/-- From every node state `before`, some block is an outcome of `gfHeadFrom` at slot `s`. -/
private theorem gfHeadFrom_nonempty_itu (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) : ∃ H, Restated.gfHeadFrom M S before s ⇢ H := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_itu _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty_itu facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_itu _ _ _).2 ⟨_, hn, hH⟩

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
    ancestor of the result `W` and the count of the late view is less than twice `sc W`; synchrony
    is assumed up to slot `s`'s support cutoff only. -/
theorem walk_eligible_of_headsBelow_at_confirmation_tick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR B)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR B)
    (hs : 0 < s) (hslo : tGAT ≤ slotStart S.E.Δ s)
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
  have hheads := Restated.coneHeads_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird
    hcs hlen hunder hunderS hprev hmv hmrlo hslo hsR hw hwaw
    (fun n' t' h1 hΔ hq h2 => hneTick n' t' h1 hΔ hq (le_trans h2 hmrc))
  have hcone := Restated.coneSupport_at_confirmation_upTo facts S Sched x hexec hsync htd hmono hcs hs hanchor
    (le_trans hgst hslo) hmv hmrlo hmrc hwaw hwh
    (fun q hq => by
      obtain ⟨H, hH⟩ := gfHeadFrom_nonempty_itu facts S (x[mv][q].st) s
      exact ⟨H, hH, hheads q hq H hH⟩)
    (hneTickVote mv hmv)
    (fun n hn => hneTick n _ hn (slotStart_emod_delta S s)
      (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwaw le_rfl (by rw [hsc]; linarith), hwh⟩)
      (by rw [hct]; linarith)) e he
  exact confWalkWith_eligible_of_cone facts S.E (Restated.confStoreAt M S (x[m][v].st) s) s
    (Restated.HonSlot M S Sched s) A e sc hscore hcone (Restated.voteSetValid_conf facts S Sched x m v s)
    hAB hpath W hW

end

end DecoupledConsensusModel.Sts.Restated
