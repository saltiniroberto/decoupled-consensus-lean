import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitConfirmUpTo
import Proofs.Claims.Restated.Claim13bStepSGMove
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitRelayUpTo
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Confirmed blocks of two action reads, with relay up to the action instant

The confirmed blocks two honest validators' round-`(r + 1)` action reads hold lie on one chain, when
the Goldfish vote relay is assumed only up to round `r + 1`'s action instant. Stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_sgMoveUpTo {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
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
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_sgMoveUpTo {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- If `a` is a member of the set `s`, then the lift of `s` can return `a`. -/
private theorem returns_lift_intro_sgMoveUpTo {α : Type} (s : Set α) (a : α) (h : a ∈ s) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  exact ⟨a, h, rfl⟩

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Stamping the clock of a store does not change which blocks pass the confirmation eligibility
    test for slot `s`. -/
private theorem confEligible_setClock_sgMoveUpTo (facts : Record.Facts M) (E : Env V) (st : M.NS)
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

/-- For every store `hs` the round-`r₁` action read can give from `before`, the block `hs` holds as
    confirmed either passes some outcome of the confirmation eligibility test of `before`'s store
    for the slot before the action instant's slot, or is the fork-choice root of `before`'s store
    stamped with the action instant. -/
private theorem actionHealingStore_live_confirmed_cases_upTo (facts : Record.Facts M)
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
        · rw [← confEligible_setClock_sgMoveUpTo facts S.E before.st
            (Restated.Vocabulary.Execution.Setup.a M S r₁)]
          refine (returns_bind_iff_sgMoveUpTo _ _ _).2 ⟨_, returns_map_intro_sgMoveUpTo _ _ _
            (returns_map_intro_sgMoveUpTo _ _ _ htm), ?_⟩
          refine (returns_bind_iff_sgMoveUpTo _ _ _).2
            ⟨score, returns_lift_intro_sgMoveUpTo _ _ hscore, ?_⟩
          exact (Record.returns_pure _ _).2 rfl
        · rw [hwalk]
          exact hel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

/-- With the Goldfish vote relay assumed only up to `S.a (r + 1)` (`hrelay`): for a store `hsv`
    round `(r + 1)`'s action can read from `v`'s node state at step `n'` and a store `hsw` it can
    read from `w`'s, if each one's confirmed block lies on one chain with `T`, each one's finalized
    block is an ancestor of `T`, and each one's justified block is an ancestor of `T` when its
    running height maximum is one more than its justified height, then the confirmed blocks of `hsv`
    and `hsw` lie on one chain. -/
theorem live_confirmed_pairwise_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n' : Nat} {v w : V} {T : NamedBlock V}
    (hrelay : Restated.GfVoteRelayAtAcceptBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (htd : Restated.TimeDiverges M x)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hv : Restated.HonestThrough M Sched x n' v) (hw : Restated.HonestThrough M Sched x n' w)
    (hvr : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hwr : w ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hawv : v ∈ Sched.awakeThroughout
      (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) - S.E.Δ)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (haww : w ∈ Sched.awakeThroughout
      (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) - S.E.Δ)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (hsv : M.HS) (hhsv : hsv ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1))
    (hsw : M.HS) (hhsw : hsw ∈ Restated.actionHealingStore M S (x[n'][w].st) (r + 1))
    (hconfv : Block.compatible hsv.live_confirmed T.erase = true)
    (hconfw : Block.compatible hsw.live_confirmed T.erase = true)
    (hFv : Block.Preceq hsv.F T.erase)
    (hFw : Block.Preceq hsw.F T.erase)
    (hJv : hsv.h_max = hsv.h_j + 1 → Block.Preceq hsv.J T.erase)
    (hJw : hsw.h_max = hsw.h_j + 1 → Block.Preceq hsw.J T.erase)
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
  classical
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn'' : Restated.tickStepAt M x n' (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn'
  -- the fork-choice roots the two fallbacks return are ancestors of `T`
  have hrootv := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][v].st) r hsv hhsv hFv hJv
  have hrootw := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][w].st) r hsw hhsw hFw hJw
  rw [hct] at hrootv hrootw
  -- each action read's confirmed block passes the eligibility test or is that root
  have hcv := actionHealingStore_live_confirmed_cases_upTo facts S (x[n'][v].st) (r + 1) hsv hhsv
  have hcw := actionHealingStore_live_confirmed_cases_upTo facts S (x[n'][w].st) (r + 1) hsw hhsw
  rw [Restated.slotOf_a_sub_one facts S (r + 1)] at hcv hcw
  rcases hcv with ⟨elv, helv, hev⟩ | hfv <;> rcases hcw with ⟨elw, helw, hew⟩ | hfw
  · exact Restated.confirmed_compatible_sts_of_gfVoteRelay_upTo facts S Sched x hexec
      (Restated.GfVoteRelayAtAcceptBefore.mono (le_of_eq hct) hrelay) htd hn''
      (facts.gr.opening_slot_pos S (Nat.succ_pos r)) hgst hv hw hawv haww helv hev helw hew
      hneTickv hneTickw
  · rw [hfw]
    exact Protocol.compatible_comm
      (Protocol.compatible_of_preceq_of_compatible hrootw (Protocol.compatible_comm hconfv))
  · rw [hfv]
    exact Protocol.compatible_of_preceq_of_compatible hrootv (Protocol.compatible_comm hconfw)
  · rw [hfv, hfw]
    exact compatible_of_preceq_common_Preceq hrootv hrootw

end

end DecoupledConsensusModel.Sts.Restated
