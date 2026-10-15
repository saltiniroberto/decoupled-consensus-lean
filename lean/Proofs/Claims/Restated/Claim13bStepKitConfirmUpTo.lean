import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bStepKitRelayUpTo
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitRelayUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Agreement of confirmations, with relay up to a cutoff

The agreement of the blocks two honest validators find eligible at one slot's confirmation, assuming
the relay of Goldfish votes only up to that confirmation instant, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- An outcome of `f <$> m` is `f a` for an outcome `a` of `m`. -/
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m >>= k` can return `b`, then `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_elim {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def] at h
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

open scoped DC in
/-- An outcome of the lift of a set `s` is a member of `s`. -/
private theorem returns_lift_elim {α : Type} (s : Set α) (a : α)
    (h : (ExceptT.lift s : DC.NDRE α) ⇢ a) : a ∈ s := by
  unfold Record.Returns at h
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨a', ha', he⟩ := h
  cases he
  exact ha'

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `confVotes_transfer` with the relay of Goldfish votes assumed only up to slot `s`'s confirmation
    instant: every vote `u` in an outcome of the votes `v`'s store counts there is in `w`'s late
    set, or `w`'s late set already shows `u`'s signer equivocating. -/
theorem confVotes_transfer_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot}
    (hrelay : Restated.GfVoteRelayAtAcceptBefore M S x (M.confirmation_time S.E s))
    (htd : Restated.TimeDiverges M x) (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {v w : V}
    (hvh : Restated.HonestThrough M Sched x n v)
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (haww : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hwh : Restated.HonestThrough M Sched x n w)
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes)
    {u : GoldfishVote V} (hu : u ∈ votes)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s ∨
      M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s)
        u.val_index = true := by
  have hΔpos : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hconf : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨h1t, h0t⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hslot, i, hi1n, -, h0, h1, hcomm, hlotime, htimebound⟩ :=
    Restated.accept_step_of_mem_confVotes facts S Sched x htd hn hpos hawv hvh hvotes hu
      hneTickv
  have hi1conf : (x[i + 1].time : Int) ≤ M.confirmation_time S.E s := by
    have hmt : (x[i + 1].time : Int) ≤ (x[n].time : Int) := Restated.time_mono_int facts S Sched x hi1n
    linarith
  have hdead : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ
      ≤ slotStart S.E.Δ s + 4 * S.E.Δ - 1 := by
    have ha : (x[i + 1].time : Int) ≤ slotStart S.E.Δ s + 3 * S.E.Δ - 1 := by linarith
    have hb : S.E.t_GST ≤ slotStart S.E.Δ s + 3 * S.E.Δ - 1 := by linarith
    have hm := max_le ha hb
    linarith
  have hA : slotStart S.E.Δ s - S.E.Δ ≤ (x[i].time : Int) := by
    have hsucc := Restated.time_succ_le facts S Sched x i
    linarith
  have hB : (x[i].time : Int) ≤ M.confirmation_time S.E s :=
    le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ i)) hi1conf
  have hawi : AtomicAwake x i w := mem_awake_of_awakeThroughout Sched haww hA hB
  have hvhi : Restated.HonestThrough M Sched x i v := fun t ht =>
    hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_of_succ_le hi1n)))
  have hawTw : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot - 1)
      (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ) := by
    rw [hslot]
    refine awakeThroughout_mono Sched haww (by omega) ?_
    rw [hconf]; linarith
  have hhi : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ slotStart S.E.Δ (u.slot + 2) := by
    rw [hslot]
    have hr : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
      have h := slotStart_add S.E.Δ s 2
      push_cast at h
      linarith
    rw [hr]; linarith
  obtain ⟨k, hk0, hk1, hres⟩ :=
    Restated.gfVote_in_pool_of_accepts_upTo facts S Sched x
      (Restated.GfVoteRelayAtAcceptBefore.mono (le_trans hdead (by rw [hconf]; linarith)) hrelay)
      htd h0 h1 hvhi hawi hcomm
      (by rw [hslot]; exact hpos) (by rw [hslot]; exact hlotime) hawTw
      (by rw [hslot]; exact hwh _ (by linarith)) hhi
      (by
        rw [hslot]
        exact fun n' ht => hneTickw n' _ ht (slotStart_emod_delta S s)
          (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched haww (by linarith)
            (by rw [hconf]; linarith), hwh _ (by linarith)⟩)
          le_rfl (by rw [hconf]; linarith))
  have hkn : k + 1 ≤ n := by
    have hxk : (x[k].time : Int) < (x[n].time : Int) := by
      rw [hconf] at h0t
      linarith
    by_contra hcon
    have hnk : n ≤ k := by omega
    have hmt := Restated.time_mono_int facts S Sched x hnk
    linarith
  rcases hres with ⟨hmem, -⟩ | heq
  · left
    have hpooln : u ∈ (M.store_pool (x[n][w].st).st.core u.slot) :=
      Restated.mem_pool_mono_sts facts S Sched x w hkn hmem
    rw [Restated.confLate_eq_pool_at_confirmation facts S Sched x hn w, ← hslot]
    exact hpooln
  · right
    have hsub : (M.store_pool (x[k][w].st).st.core u.slot)
        ⊆ Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s := by
      rw [Restated.confLate_eq_pool_at_confirmation facts S Sched x hn w, ← hslot]
      intro z hz
      have hzs : z.slot = u.slot := Restated.slot_of_mem_pool_sts facts S Sched x k w hz
      have hz' : z ∈ (M.store_pool (x[k][w].st).st.core z.slot) := by rw [hzs]; exact hz
      have hzn : z ∈ (M.store_pool (x[n][w].st).st.core z.slot) :=
        Restated.mem_pool_mono_sts facts S Sched x w (Nat.le_of_succ_le hkn) hz'
      rw [← hzs]; exact hzn
    exact facts.sch.equivocates_mono_of_subset hsub heq

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `crossView_sts` with the relay of Goldfish votes assumed only up to slot `s`'s confirmation
    instant. -/
theorem crossView_sts_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {n : Nat} {s : Slot}
    (hrelay : Restated.GfVoteRelayAtAcceptBefore M S x (M.confirmation_time S.E s))
    (htd : Restated.TimeDiverges M x) (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {v w : V}
    (hv : Restated.HonestThrough M Sched x n v) (hw : Restated.HonestThrough M Sched x n w)
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (haww : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E (x[n][v].st).st.core s ⇢ votes)
    (hneTickv : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n'] v) t ⇢ out)
    (hneTickw : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n'] w) t ⇢ out) :
    Restated.Vocabulary.Protocol.CrossView M (x[n][v].st).st.core.T (x[n][w].st).st.core.T
      votes
      (Restated.Vocabulary.Protocol.confLate M S.E (x[n][w].st).st.core s) where
  transfer := fun _ hu =>
    Restated.confVotes_transfer_upTo facts S Sched x hrelay htd hn hpos hgst hv hawv haww hw
      hvotes hu hneTickv hneTickw
  resolve := fun _ _ _ _ hB hC => Restated.find?_eq_of_bodies facts S Sched x hexec hv hw hB hC

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `confirmed_compatible_sts_of_gfVoteRelay` with the relay of Goldfish votes assumed only up to
    slot `s`'s confirmation instant: blocks `B` and `C` that outcomes of `v`'s and `w`'s
    confirmation tests pass lie on one chain. -/
theorem confirmed_compatible_sts_of_gfVoteRelay_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {n : Nat} {s : Slot}
    (hrelay : Restated.GfVoteRelayAtAcceptBefore M S x (M.confirmation_time S.E s))
    (htd : Restated.TimeDiverges M x) (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hpos : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {v w : V}
    (hv : Restated.HonestThrough M Sched x n v) (hw : Restated.HonestThrough M Sched x n w)
    (hawv : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (haww : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
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
  obtain ⟨votesv, hvv, hrv⟩ := returns_bind_elim _ _ _ helv
  obtain ⟨scv, hscv, hpv⟩ := returns_bind_elim _ _ _ hrv
  have hscv' := returns_lift_elim _ _ hscv
  rw [Record.returns_pure] at hpv
  subst hpv
  obtain ⟨votesw, hvw', hrw⟩ := returns_bind_elim _ _ _ helw
  obtain ⟨scw, hscw, hpw⟩ := returns_bind_elim _ _ _ hrw
  have hscw' := returns_lift_elim _ _ hscw
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
  have hvw := Restated.crossView_sts_upTo facts S Sched x hexec hrelay htd hn hpos hgst hv hw
    hawv haww hvv hneTickv hneTickw
  have hwv := Restated.crossView_sts_upTo facts S Sched x hexec hrelay htd hn hpos hgst hw hv
    haww hawv hvw' hneTickw hneTickv
  obtain ⟨ev, hev, rfl⟩ := returns_map_elim _ _ _ hvv
  obtain ⟨tmv, htmv, rfl⟩ := returns_map_elim _ _ _ hev
  obtain ⟨ew, hew, rfl⟩ := returns_map_elim _ _ _ hvw'
  obtain ⟨tmw, htmw, rfl⟩ := returns_map_elim _ _ _ hew
  exact facts.fc.eligible_compatible
    (fun u hu => hel _ tmv htmv u hu) rfl (fun u hu => hel _ tmw htmw u hu) rfl
    hvw.transfer hvw.resolve hwv.transfer hwv.resolve
    _ (hscv' B) hB _ (hscw' C) hC

end

end DecoupledConsensusModel.Sts.Restated
