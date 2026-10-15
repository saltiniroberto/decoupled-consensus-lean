import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepConeUpTo
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# The confirmed block a round's action reads, with synchrony up to a cutoff

The theorem that the confirmed block round `r + 1`'s action reads lies on one chain with the
round-`r` anchor, assuming synchrony only up to the support cutoff of round `r + 1`'s opening slot,
stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Execution

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_iterUpTo {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_iterUpTo {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- `gfHeadWith` has an outcome at every store. -/
private theorem gfHeadWith_nonempty_iterUpTo (facts : Record.Facts M) (contract : M.Contract)
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
  exact (returns_bind_iff_iterUpTo _ _ _).2 ⟨T, hT, (returns_bind_iff_iterUpTo _ _ _).2
    ⟨W, hW, (returns_bind_iff_iterUpTo _ _ _).2 ⟨U, hU,
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH⟩⟩⟩

/-- `gfHeadFrom` at slot `s` has an outcome from every node state. -/
private theorem gfHeadFrom_nonempty_iterUpTo (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) : ∃ H, Restated.gfHeadFrom M S before s ⇢ H := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_iterUpTo _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty_iterUpTo facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_iterUpTo _ _ _).2 ⟨_, hn, hH⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `live_confirmed_compatible_at_action` with synchrony assumed only up to the support cutoff of
    round `r + 1`'s opening slot: the confirmed block of every store round `r + 1`'s action can read
    from `v`'s node state at step `n` lies on one chain with `T`'s block. -/
theorem live_confirmed_compatible_at_action_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))))) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {v : V} {T : NamedBlock V}
    (hanchor : tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hawTc : v ∈ Sched.awakeThroughout (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) v)
    (hprev : Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1))))
    (hres : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      Restated.HeadsResolve M S Sched x v m n ((M.opening_slot S.hc (r + 1))))
    (hid : Restated.TreeIdealizes M S Sched x v n T.erase)
    (hinlog : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ v' ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∀ G : Block V,
        Restated.gfHeadFrom M S (x[m][v'].st) ((M.opening_slot S.hc (r + 1))) ⇢ G →
        ∃ H : NamedBlock V, Restated.blockInLog M S Sched x H ∧ H.erase = G)
    (hvalid : Protocol.VoteSetValid S.E ((M.opening_slot S.hc (r + 1)))
      (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))
        ((M.opening_slot S.hc (r + 1)))))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n][v].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A)
    (hAB : Block.Preceq A T.erase)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C T.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))))
    (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S (x[n][v].st) (r + 1))
    (hF : Block.Preceq hs.F T.erase)
    (hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J T.erase = true)
    (hneTickVote : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ q ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) x[m] q) (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hneTick : ∀ n' : Nat, Restated.tickStepAt M x n' (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))) x[n'] v) (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) x[n] v) (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))) x[n] v)
      (M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1))) :
    Block.compatible hs.live_confirmed T.erase = true := by
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn' : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn
  have hd := S.E.Δ_pos
  have haw : v ∈ Sched.awake (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) :=
    mem_awake_of_awakeThroughout Sched hawTc
      (by
        have := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        linarith)
      (le_refl _)
  have hbridge : hs.live_confirmed = (x[n + 1][v].st).st.core.live_confirmed :=
    Restated.actionHealingStore_live_confirmed facts S Sched x hct
      (Restated.slotOf_a_sub_one facts S (r + 1)) hn'
      (Finset.mem_sdiff.2 ⟨haw, hvh _ (le_refl _)⟩) hneTickConf hrun hs hhs
  have hsopen : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd
    (facts.sch.vote_time_pos S hsopen)
  have hcone := Restated.coneHeads_of_headsBelow facts S Sched x hprev hm (hres m hm) hid
    (hinlog m hm)
  have hcases := Restated.live_confirmed_cases_of_cone_upTo facts S Sched x hexec hsync htd
    hmono hcs hsopen hanchor hgst hm hn' hawTc hvh
    (fun q hq => by
      obtain ⟨H, hH⟩ := gfHeadFrom_nonempty_iterUpTo facts S (x[m][q].st)
        (M.opening_slot S.hc (r + 1))
      exact ⟨H, hH, hcone q hq H hH⟩)
    hvalid c hc A hA hAB hpath (hneTickVote m hm) hneTick hneTickConf hrun
  rw [hbridge]
  rcases hcases with hpre | heq
  · exact Block.compatible_of_preceq_common (Block.preceq_self _)
      (preceq_eq_true_iff_Preceq.mpr hpre)
  · rw [heq]
    obtain ⟨c', hc', X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S (x[n][v].st) (r + 1) hs hhs
    obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
      Restated.HS_fields_store_with_cache facts c' hst₀
    simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
    rw [Record.Model.HS.F, facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ X hX,
      facts.hd.setClock_toHealing_F] at hF
    rw [Record.Model.HS.h_max, Record.Model.HS.h_j, Record.Model.HS.J,
      facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ X hX,
      facts.dt.update_confirmation_with_toHealing_h_j _ _ _ _ _ X hX,
      facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ X hX,
      facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j,
      facts.hd.setClock_toHealing_J] at hJ
    have hF' : Block.Preceq
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).F T.erase := by
      rw [Restated.confStoreAt, Record.Model.HS.F, facts.hd.setClock_toHealing_F]
      exact hF
    have hJ' : (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).h_max
        = (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).h_j + 1 →
        Block.compatible
        (M.toHealing (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1))))).J T.erase
        = true := by
      rw [Restated.confStoreAt, Record.Model.HS.h_max, Record.Model.HS.h_j, Record.Model.HS.J,
        facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J]
      exact hJ
    exact facts.fc.fgRoot_compatible_ofJustifiedBranch hF' hJ'

end

end DecoupledConsensusModel.Sts.Restated
