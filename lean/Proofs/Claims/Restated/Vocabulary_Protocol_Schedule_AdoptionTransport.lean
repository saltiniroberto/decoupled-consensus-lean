import Proofs.Vocabulary.Protocol.Schedule.AdoptionTransport
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Schedule_AdoptionTransport
import Model.Record.Wiring

/-!
# Settling a Goldfish vote before a cutoff

Processing a Goldfish vote before a cutoff pools it before the cutoff or exposes its validator's
equivocation, pool carries keep the votes before a cutoff, and a vote settled before a freeze is
visible in the next voter views, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- If `st` carries its pool stamps, `u`'s slot is neither expired nor in the future for `st`, and
    `st`'s clock is before `Γ`, then after `M.on_goldfish_vote st u` the vote `u` is in its slot's
    pool stamped before `Γ`, or its validator equivocates among the votes of that pool stamped
    before `Γ`. -/
theorem Vocabulary.Protocol.on_goldfish_vote_beforeCutoff_or_equivocates (facts : Record.Facts M)
    (st : M.S) (u : GoldfishVote V) (Γ : Time)
    (hstamps : Restated.Vocabulary.Protocol.PoolStamps M st)
    (hfresh : ¬ u.slot < st.s - 1) (hfuture : ¬ st.s < u.slot)
    (hclock : st.t < Γ) :
    u ∈ beforeCutoff (M.on_goldfish_vote st u).timestamp_vote Γ
        ((M.store_pool (M.on_goldfish_vote st u) u.slot)) ∨
      M.equivocates
        (beforeCutoff (M.on_goldfish_vote st u).timestamp_vote Γ
          ((M.store_pool (M.on_goldfish_vote st u) u.slot))) u.val_index = true :=
  facts.hd.on_goldfish_vote_beforeCutoff_or_equivocates st u Γ hstamps hfresh hfuture hclock

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- If `u`'s validator is in its slot's committee, `st` carries its pool stamps, `u`'s slot is
    neither expired nor in the future for `st`, and `st`'s clock is before `Γ`, then after
    `M.on_goldfish_vote_checked E st u` the vote `u` is in its slot's pool stamped before `Γ`, or
    its validator equivocates among the votes of that pool stamped before `Γ`. -/
theorem Vocabulary.Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates (facts : Record.Facts M)
    (E : Env V) (st : M.S) (u : GoldfishVote V) (Γ : Time)
    (hcommittee : u.val_index ∈ E.committee u.slot)
    (hstamps : Restated.Vocabulary.Protocol.PoolStamps M st)
    (hfresh : ¬ u.slot < st.s - 1) (hfuture : ¬ st.s < u.slot)
    (hclock : st.t < Γ) :
    u ∈ beforeCutoff
          (M.on_goldfish_vote_checked E st u).timestamp_vote Γ
          ((M.store_pool (M.on_goldfish_vote_checked E st u) u.slot)) ∨
      M.equivocates
        (beforeCutoff
          (M.on_goldfish_vote_checked E st u).timestamp_vote Γ
          ((M.store_pool (M.on_goldfish_vote_checked E st u) u.slot)))
        u.val_index = true := by
  rw [facts.hd.on_goldfish_vote_checked_of_mem_committee E st u hcommittee]
  exact Restated.Vocabulary.Protocol.on_goldfish_vote_beforeCutoff_or_equivocates facts st u Γ hstamps
    hfresh hfuture hclock

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- If `st'` keeps every vote and every stamp of `st`, then for every slot `k` and cutoff `Γ`, the
    votes of `st`'s slot-`k` pool stamped before `Γ` are among the votes of `st'`'s slot-`k` pool
    stamped before `Γ`. -/
theorem Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry (facts : Record.Facts M)
    {st st' : M.S}
    (hcarry : Restated.Vocabulary.Protocol.PoolCarry M st st') (k : Slot) (Γ : Time) :
    beforeCutoff st.timestamp_vote Γ (M.store_pool st k) ⊆
      beforeCutoff st'.timestamp_vote Γ (M.store_pool st' k) := by
  intro u hu
  rw [beforeCutoff, Finset.mem_filter, facts.sto.mem_pool_iff] at hu ⊢
  refine ⟨hcarry.mem k u hu.1, ?_⟩
  cases hc : st.timestamp_vote u with
  | none => rw [stampedBefore, hc] at hu; simp at hu
  | some c =>
      simp only [stampedBefore, hc, decide_eq_true_eq] at hu
      simp only [stampedBefore, hcarry.stamp u c hc, decide_eq_true_eq]
      exact hu.2

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- If the head `H` of the Goldfish vote `u` is in `st`'s tree, stamped before the slot-`s` freeze,
    of a slot at most `u`'s, and `u` was received before that freeze or its signer equivocates among
    the slot-`s` votes received before it, then for every outcome `U` of the voter's support view of
    slot `s + 1` and every outcome `Y` of the voter's view of slot `s + 1`, `u ∈ U` or `u`'s signer
    equivocates in `Y`. -/
theorem Vocabulary.Protocol.settled_before_freeze_in_voter_pair (facts : Record.Facts M)
    (E : Env V) (st : M.S) (s : Slot) {u : GoldfishVote V}
    {H : Block V} (hfind : Block.find? st.T u.head = some H)
    (hH : stampedBefore st.timestamp_block (M.view_freeze E s) H = true)
    (hslot : H.slot ≤ u.slot)
    (hsettled :
      u ∈ beforeCutoff st.timestamp_vote (M.view_freeze E s) ((M.store_pool st s)) ∨
        M.equivocates
          (beforeCutoff st.timestamp_vote (M.view_freeze E s) ((M.store_pool st s)))
          u.val_index = true) :
    ∀ U : Finset (GoldfishVote V),
      M.voter_support_view E (M.toHealing st).toFG.toSG.toGoldfishStore (s + 1) ⇢ U →
    ∀ Y : Finset (GoldfishVote V),
      M.voter_view E (M.toHealing st).toFG.toSG.toGoldfishStore (s + 1) ⇢ Y →
    u ∈ U ∨ M.equivocates Y u.val_index = true := by
  intro U hU Y hY
  rcases hsettled with hrecv | hequiv
  · apply Or.inl
    rw [beforeCutoff, Finset.mem_filter] at hrecv
    obtain ⟨hpool, hst⟩ := hrecv
    cases hc : st.timestamp_vote u with
    | none => rw [stampedBefore, hc] at hst; simp at hst
    | some c =>
        simp only [stampedBefore, hc, decide_eq_true_eq] at hst
        cases hb : st.timestamp_block H with
        | none => rw [stampedBefore, hb] at hH; simp at hH
        | some σ =>
            simp only [stampedBefore, hb, decide_eq_true_eq] at hH
            exact facts.sch.mem_voter_support_view_of_pool E (M.toHealing st).toFG.toSG.toGoldfishStore s
              (by show u ∈ M.gs_pool _ s; rw [facts.sto.toHealing_gs_pool]; exact hpool)
              (by rw [facts.sto.toHealing_gs_timestamp_vote]; exact hc) hst
              (by rw [facts.sto.toHealing_gs_T]; exact hfind) hslot
              (by rw [facts.sto.toHealing_gs_timestamp_block]; exact hb) hH U hU
  · apply Or.inr
    apply facts.sch.equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [beforeCutoff, Finset.mem_filter] at hx
    cases hc : st.timestamp_vote x with
    | none => rw [stampedBefore, hc] at hx; simp at hx
    | some c =>
        simp only [stampedBefore, hc, decide_eq_true_eq] at hx
        apply facts.fc.mem_voter_view_of_pool E (M.toHealing st).toFG.toSG.toGoldfishStore s
          (τ := c)
        · show x ∈ M.gs_pool _ s
          rw [facts.sto.toHealing_gs_pool]; exact hx.1
        · rw [facts.sto.toHealing_gs_timestamp_vote]; exact hc
        · exact hx.2
        · exact hY

end

end DecoupledConsensusModel.Sts.Restated
