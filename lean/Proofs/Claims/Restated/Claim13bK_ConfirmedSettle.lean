import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettle

/-!
# Confirmed blocks that settle on honest votes

How `AncestorOfHonestHeadsFrom` passes to ancestors, to later slots and through the routines that
update the stable and confirmed records, and what the tick at a slot's confirmation time writes to
those records, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest active committee member of every slot from `s` on votes for a descendant of `B`,
    and `X` is an ancestor of `B`, the same holds of `X`. -/
theorem ancestorOfHonestHeadsFrom_of_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {X B : Block V} {s : Slot}
    (hXB : Block.Preceq X B) (h : Restated.AncestorOfHonestHeadsFrom M S Sched x B s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x X s :=
  fun s' hs' => Restated.headsBelow_mono facts S Sched x hXB (h s' hs')

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest active committee member of every slot from `s` on votes for a descendant of `B`,
    the same holds from any slot `s' ≥ s` on. -/
theorem ancestorOfHonestHeadsFrom_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {B : Block V} {s s' : Slot} (hss' : s ≤ s')
    (h : Restated.AncestorOfHonestHeadsFrom M S Sched x B s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x B s' :=
  fun s'' hs'' => h s'' (le_trans hss' hs'')

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `G` has `AncestorOfHonestHeadsFrom` from `s`, and `old` has it whenever `G` is an ancestor of
    `old`, then `advance_confirmed old G` has it from `s`. -/
theorem ancestorOfHonestHeadsFrom_advance_confirmed (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {old G : Block V} {s : Slot}
    (hG : Restated.AncestorOfHonestHeadsFrom M S Sched x G s)
    (hold : Block.Preceq G old → Restated.AncestorOfHonestHeadsFrom M S Sched x old s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (M.advance_confirmed old G) s := by
  rcases facts.hd.advance_confirmed_values old G with ⟨h, he⟩ | he
  · rw [he]; exact hold h
  · rw [he]; exact hG

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `stable` has `AncestorOfHonestHeadsFrom` from `s`, and the candidate and `old` each have it
    whenever they are descendants of `stable`, then the block `floor_on_stable stable candidate old`
    returns has it from `s`. -/
theorem ancestorOfHonestHeadsFrom_floor_on_stable (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {stable candidate old : Block V} {s : Slot}
    (hst : Restated.AncestorOfHonestHeadsFrom M S Sched x stable s)
    (hcand : Block.Preceq stable candidate → Restated.AncestorOfHonestHeadsFrom M S Sched x candidate s)
    (hold : Block.Preceq stable old → Restated.AncestorOfHonestHeadsFrom M S Sched x old s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (M.floor_on_stable stable candidate old) s := by
  rcases facts.hd.floor_on_stable_values stable candidate old with ⟨h1, he⟩ | ⟨h2, he⟩ | he
  · rw [he]; exact hcand h1
  · rw [he]; exact hold h2
  · rw [he]; exact hst

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a store's `latest_stable` and its finalized block `F` both have `AncestorOfHonestHeadsFrom`
    from `s`, so does `get_stable` of the store. -/
theorem ancestorOfHonestHeadsFrom_get_stable (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (st : M.S) {s : Slot}
    (hL : Restated.AncestorOfHonestHeadsFrom M S Sched x st.latest_stable s)
    (hF : Restated.AncestorOfHonestHeadsFrom M S Sched x st.F s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_stable st) s := by
  rcases facts.hd.get_stable_eq_or st with he | he
  · rw [he]; exact hL
  · rw [he]; exact hF

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a store's `get_stable` has `AncestorOfHonestHeadsFrom` from `s`, and its `latest_confirmed`
    has it whenever it is a descendant of `get_stable`, then `get_confirmed` of the store has it
    from `s`. -/
theorem ancestorOfHonestHeadsFrom_get_confirmed (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (st : M.S) {s : Slot}
    (hS : Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_stable st) s)
    (hC : Block.Preceq (M.get_stable st) st.latest_confirmed →
      Restated.AncestorOfHonestHeadsFrom M S Sched x st.latest_confirmed s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_confirmed st) s := by
  rcases facts.hd.get_confirmed_values st with ⟨h, he⟩ | he
  · rw [he]; exact hC h
  · rw [he]; exact hS

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At a time `t` of a slot `s > 0` that is slot `s`'s support cutoff and neither its proposal time
    nor its Goldfish vote time, if `n` passes the grade-2 awake test of the round of `s` under
    `Setup.alwaysAwake S`, then for every outcome `out` of `v`'s tick at `t` from `n`, every outcome
    `c` of the cache update and every outcome `D` of the confirmation update for slot `s - 1` under
    `c`'s grade contract on `n`'s store with its clock set to `t`, the store of `out.1` holds the
    `latest_stable` and the `latest_confirmed` of `D`. -/
theorem namedTick_records_at_confirmation (facts : Record.Facts M)
    (S : Setup V) (v : V) (n : M.N) (t : Int)
    (hspos : 0 < S.E.slotOf t)
    (hnp : t ≠ M.proposal_time S.E (S.E.slotOf t))
    (hnv : t ≠ M.vote_time S.E (S.E.slotOf t))
    (hsc : t = M.support_cutoff S.E (S.E.slotOf t))
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v n (M.round_of S.hc (S.E.slotOf t)))
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    (D : M.S) (hD : M.update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E n.st t).core (S.E.slotOf t - 1) ⇢ D) (hn : M.reachedNode n := by trivial) :
    out.1.st.core.latest_stable = D.latest_stable ∧
      out.1.st.core.latest_confirmed = D.latest_confirmed :=
  facts.nd.tick_records_at_confirmation_of_outcomes S v n t hspos hnp hnv hsc hrun out hout c hc D hD

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Right after the tick at slot `s`'s confirmation time, a validator `w` awake there and outside
    the adversary's set, whose tick has an outcome, holds as `latest_stable` the block
    `advance_confirmed` of the `latest_stable` it held before with the stable root `G` of its grade
    contract, and as `latest_confirmed` the `latest_confirmed` of every outcome of the confirmation
    update at `s`. -/
theorem records_after_confirmation_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot}
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1))) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
        (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c →
    ∀ o : Option (Block V), (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ o →
    ∃ G : Block V, o = some G ∧
      (x[n + 1][w].st).st.core.latest_stable
        = M.advance_confirmed (x[n][w].st).st.core.latest_stable G ∧
      ∀ D : M.S, M.update_confirmation_with (M.gradeContract c) S.E S.hc
            (M.ns_setClock S.E (x[n][w].st).st
              (M.confirmation_time S.E s)).core s ⇢ D →
        (x[n + 1][w].st).st.core.latest_confirmed = D.latest_confirmed := by
  have _hr_0 : M.reachedNode (x[n + 1][w].st) := Record.reachedNode_sts facts S Sched x (n + 1) w
  have _hr_1 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  have _hr_2 : M.reachedNode (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) := Record.reachedNode_wakeStage facts S Sched x n w (M.confirmation_time S.E s)
  intro c hc o ho
  obtain ⟨t', hlbl, ht'⟩ := hn
  have hslot : S.E.slotOf (M.confirmation_time S.E s) = s + 1 :=
    facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hcs : M.confirmation_time S.E s = M.support_cutoff S.E (s + 1) :=
    facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hcs]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  obtain ⟨out, hout, hst⟩ : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w)
          (M.confirmation_time S.E s) ⇢ out ∧
        x[n + 1][w].st = out.1 := by
    rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' hdvd with
      ⟨out, hout, h⟩ | ⟨hno, -⟩
    · rw [ht'] at hout
      exact ⟨out, hout, h⟩
    · obtain ⟨out, hout⟩ := hneTick
      rw [← ht'] at hout
      exact absurd hout (hno out)
  have hsc : M.confirmation_time S.E s
      = M.support_cutoff S.E (S.E.slotOf (M.confirmation_time S.E s)) := by
    rw [hslot]
    exact hcs
  have hnp : M.confirmation_time S.E s
      ≠ M.proposal_time S.E (S.E.slotOf (M.confirmation_time S.E s)) := by
    rw [hslot, hcs]
    exact facts.sch.support_cutoff_ne_proposal_time S.E (s + 1)
  have hnv : M.confirmation_time S.E s
      ≠ M.vote_time S.E (S.E.slotOf (M.confirmation_time S.E s)) := by
    rw [hslot, hcs]
    exact facts.sch.support_cutoff_ne_vote_time S.E (s + 1)
  have hrec : ∀ D : M.S, M.update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][w].st).st (M.confirmation_time S.E s)).core s ⇢ D →
      out.1.st.core.latest_stable = D.latest_stable ∧
        out.1.st.core.latest_confirmed = D.latest_confirmed := by
    intro D hD
    have hD' : M.update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][w].st).st (M.confirmation_time S.E s)).core
        (S.E.slotOf (M.confirmation_time S.E s) - 1) ⇢ D := by
      rw [hslot, Nat.add_sub_cancel]; exact hD
    exact Restated.namedTick_records_at_confirmation facts (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w)
      (M.confirmation_time S.E s) (show 0 < S.E.slotOf (M.confirmation_time S.E s) by
        rw [hslot]; exact Nat.succ_pos s) hnp hnv hsc
      (by have h := hrun; rw [← hslot] at h; exact h)
      out hout c
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) D
      (by rw [Record.wakeStage_st facts]; exact hD')
  -- `frameStableRoot` answers `some` in both of its cases.
  obtain ⟨G, rfl⟩ := facts.gr.frameStableRoot_exists _ _ _ _ _ o
    ((facts.nd.gradeContract_stableRoot _ _ _ _ _ o).1 ho)
  refine ⟨G, rfl, ?_, ?_⟩
  · obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][w].st).st (M.confirmation_time S.E s)).core s
    rw [hst, (hrec D hD).1,
      facts.hd.update_confirmation_with_latest_stable_of_root _ _ _ _ _ (some G) ho rfl D hD,
      facts.hd.setClock_core_latest_stable]
  · intro D hD
    rw [hst, (hrec D hD).2]

end

end DecoupledConsensusModel.Sts.Restated
