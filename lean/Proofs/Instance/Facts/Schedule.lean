import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Instance.Equalities.ForkChoiceImages

/-!
# The schedule family's facts at `Model.spec`

Proofs of the fields of `ScheduleFacts` at `Model.spec`, one theorem `spec_<field>` per
field, mostly by rewriting each member to its value at `Model.vocabulary`, and the bundle
`Model.spec_runFacts_schedule`.
-/

set_option autoImplicit false

namespace SpecRecord.ScheduleFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution (Setup)
open DecoupledConsensusModel.Protocol (HealConfig)
open SpecRecord.ChainStateToHandlers (unreadEnv goldfishVoteToSpecEmb)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The members the fields name, at `Model.spec` and at `Model.vocabulary` -/

/-- The member `proposal_time` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem proposal_time_spec (E : Env V) (s : Slot) :
    (Model.spec (V := V)).proposal_time E s = (Model.vocabulary (V := V)).proposal_time E s :=
  (toProof_proposal_time E unreadHealConfig unreadHeightConfig s).symm

/-- The member `vote_time` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem vote_time_spec (E : Env V) (s : Slot) :
    (Model.spec (V := V)).vote_time E s = (Model.vocabulary (V := V)).vote_time E s :=
  (toProof_vote_time E unreadHealConfig unreadHeightConfig s).symm

/-- The member `support_cutoff` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem support_cutoff_spec (E : Env V) (s : Slot) :
    (Model.spec (V := V)).support_cutoff E s = (Model.vocabulary (V := V)).support_cutoff E s :=
  (toProof_support_cutoff E unreadHealConfig unreadHeightConfig s).symm

/-- The member `view_freeze` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem view_freeze_spec (E : Env V) (s : Slot) :
    (Model.spec (V := V)).view_freeze E s = (Model.vocabulary (V := V)).view_freeze E s :=
  (toProof_view_freeze E unreadHealConfig unreadHeightConfig s).symm

/-- The member `confirmation_time` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem confirmation_time_spec (E : Env V) (s : Slot) :
    (Model.spec (V := V)).confirmation_time E s =
      (Model.vocabulary (V := V)).confirmation_time E s :=
  (toProof_confirmation_time E unreadHealConfig unreadHeightConfig s).symm

/-- The member `round_of` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem round_of_spec (hc : HealConfig) (s : Slot) :
    (Model.spec (V := V)).round_of hc s = (Model.vocabulary (V := V)).round_of hc s :=
  (toProof_round_of (unreadEnv (V := V)) hc unreadHeightConfig s).symm

/-- The member `opening_slot` is the same at `Model.spec` and at `Model.vocabulary`: both are
    `r * hc.R`. -/
private theorem opening_slot_spec (hc : HealConfig) (r : Round) :
    (Model.spec (V := V)).opening_slot hc r = (Model.vocabulary (V := V)).opening_slot hc r := by
  show r * hc.R = hc.opening_slot r
  unfold DecoupledConsensusModel.Protocol.HealConfig.opening_slot
  rfl

/-- The member `a` is the same at `Model.spec` and at `Model.vocabulary`: both are
    `4 * Δ * (r * hc.R) + 6 * Δ`. -/
private theorem a_spec (hc : HealConfig) (Δ : Time) (r : Round) :
    (Model.spec (V := V)).a hc Δ r = (Model.vocabulary (V := V)).a hc Δ r := by
  show 4 * Δ * ((r * hc.R : Slot) : Time) + 6 * Δ = hc.a Δ r
  unfold DecoupledConsensusModel.Protocol.HealConfig.a
    DecoupledConsensusModel.Protocol.HealConfig.opening_slot slotStart
  rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Mapping a set of Goldfish votes to their spec forms and back gives the set. -/
private theorem votes_map_toSpec_toProof (votes : Finset (GoldfishVote V)) :
    (votes.map goldfishVoteToSpecEmb).map Spec.GoldfishVote.toProofEmb = votes := by
  ext u
  simp [goldfishVoteToSpecEmb]

/-- The member `votes_by` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem votes_by_spec (votes : Finset (GoldfishVote V)) (v : V) :
    (Model.spec (V := V)).votes_by votes v = (Model.vocabulary (V := V)).votes_by votes v := by
  show (Spec.Protocol.votes_by (votes.map goldfishVoteToSpecEmb) v).map
    Spec.GoldfishVote.toProofEmb = Protocol.votes_by votes v
  rw [← toProof_votes_by, votes_map_toSpec_toProof]

/-- The member `equivocates` is the same at `Model.specBase` and at `Model.vocabulary`. -/
private theorem equivocates_spec_base (votes : Finset (GoldfishVote V)) (v : V) :
    (Model.specBase (V := V)).equivocates votes v =
      (Model.vocabulary (V := V)).equivocates votes v := by
  show Spec.Protocol.equivocates (votes.map goldfishVoteToSpecEmb) v =
    Protocol.equivocates votes v
  rw [← toProof_equivocates, votes_map_toSpec_toProof]

/-- The member `equivocates` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem equivocates_spec (votes : Finset (GoldfishVote V)) (v : V) :
    (Model.spec (V := V)).equivocates votes v =
      (Model.vocabulary (V := V)).equivocates votes v := by
  show Spec.Protocol.equivocates (votes.map goldfishVoteToSpecEmb) v =
    Protocol.equivocates votes v
  rw [← toProof_equivocates, votes_map_toSpec_toProof]

/-- The member `participates` is the same at `Model.spec` and at `Model.vocabulary`. -/
private theorem participates_spec (votes : Finset (GoldfishVote V)) (v : V) :
    (Model.spec (V := V)).participates votes v =
      (Model.vocabulary (V := V)).participates votes v := by
  show Spec.Protocol.participates (votes.map goldfishVoteToSpecEmb) v =
    Protocol.participates votes v
  rw [← toProof_participates, votes_map_toSpec_toProof]

/-! ## The fields -/

/-- The field `round_of_slotOf_a` of `ScheduleFacts` at `Model.spec`: the round of the slot of
    round `r`'s action time is `r`. -/
theorem spec_round_of_slotOf_a : ∀ (S : Setup V) (r : Round), (Model.spec (V := V)).round_of S.hc (S.E.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r)) = r := by
  simp only [round_of_spec, a_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).round_of_slotOf_a

/-- The field `slotStart_add_six_delta_eq_confirmation_time` of `ScheduleFacts` at
    `Model.spec`: the confirmation time of slot `s` is the start of slot `s` plus `6Δ`. -/
theorem spec_slotStart_add_six_delta_eq_confirmation_time : ∀ (E : Env V) (s : Slot),
    slotStart E.Δ s + 6 * E.Δ = (Model.spec (V := V)).confirmation_time E s := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotStart_add_six_delta_eq_confirmation_time

/-- The field `slotStart_add_delta_eq_vote_time` of `ScheduleFacts` at `Model.spec`: the
    Goldfish vote time of slot `s` is the start of slot `s` plus `Δ`. -/
theorem spec_slotStart_add_delta_eq_vote_time : ∀ (E : Env V) (s : Slot),
    slotStart E.Δ s + E.Δ = (Model.spec (V := V)).vote_time E s := by
  simp only [vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotStart_add_delta_eq_vote_time

/-- The field `vote_time_succ_add_delta_le_confirmation_time` of `ScheduleFacts` at
    `Model.spec`: the Goldfish vote time of slot `s + 1`, plus one delay, is at most the
    confirmation time of `s`. -/
theorem spec_vote_time_succ_add_delta_le_confirmation_time : ∀ (E : Env V) (s : Slot),
    (Model.spec (V := V)).vote_time E (s + 1) + E.Δ ≤ (Model.spec (V := V)).confirmation_time E s := by
  simp only [vote_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_succ_add_delta_le_confirmation_time

/-- The field `a_add_delta_eq_view_freeze` of `ScheduleFacts` at `Model.spec`: one delay after
    the action time of round `r` is the view freeze of the slot after round `r`'s opening slot. -/
theorem spec_a_add_delta_eq_view_freeze : ∀ (S : Setup V) (r : Round), (Model.spec (V := V)).a S.hc S.E.Δ r + S.E.Δ = (Model.spec (V := V)).view_freeze S.E ((Model.spec (V := V)).opening_slot S.hc r + 1) := by
  simp only [view_freeze_spec, opening_slot_spec, a_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).a_add_delta_eq_view_freeze

/-- The field `Γ_0_eq_proposal_time` of `ScheduleFacts` at `Model.spec`: the start of the
    opening slot of round `r` is that slot's proposal time. -/
theorem spec_Γ_0_eq_proposal_time : ∀ (hc : HealConfig) (E : Env V) (r : Round), slotStart E.Δ ((Model.spec (V := V)).opening_slot hc r) = (Model.spec (V := V)).proposal_time E ((Model.spec (V := V)).opening_slot hc r) := by
  simp only [proposal_time_spec, opening_slot_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Γ_0_eq_proposal_time

/-- The field `Γ_1_eq_vote_time` of `ScheduleFacts` at `Model.spec`: one delay after the start
    of the opening slot of round `r` is that slot's Goldfish vote time. -/
theorem spec_Γ_1_eq_vote_time : ∀ (hc : HealConfig) (E : Env V) (r : Round), slotStart E.Δ ((Model.spec (V := V)).opening_slot hc r) + E.Δ = (Model.spec (V := V)).vote_time E ((Model.spec (V := V)).opening_slot hc r) := by
  simp only [vote_time_spec, opening_slot_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Γ_1_eq_vote_time

/-- The field `a_eq_confirmation_time` of `ScheduleFacts` at `Model.spec`: the action time of
    round `r` is the confirmation time of round `r`'s opening slot. -/
theorem spec_a_eq_confirmation_time : ∀ (hc : HealConfig) (E : Env V) (r : Round), (Model.spec (V := V)).a hc E.Δ r = (Model.spec (V := V)).confirmation_time E ((Model.spec (V := V)).opening_slot hc r) := by
  simp only [confirmation_time_spec, opening_slot_spec, a_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).a_eq_confirmation_time

/-- The field `confirmation_time_eq_support_cutoff_succ` of `ScheduleFacts` at `Model.spec`:
    the confirmation time of slot `s` is the support cutoff of slot `s + 1`. -/
theorem spec_confirmation_time_eq_support_cutoff_succ : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).confirmation_time E s = (Model.spec (V := V)).support_cutoff E (s + 1) := by
  simp only [support_cutoff_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).confirmation_time_eq_support_cutoff_succ

/-- The field `publicTime_iff` of `ScheduleFacts` at `Model.spec`: `t` is a public time of `S`
    exactly when `t` is the proposal time, the Goldfish vote time, the support cutoff or the view
    freeze of some slot. -/
theorem spec_publicTime_iff : ∀ (S : Setup V) (t : Time), PublicTime S t ↔
    ∃ s : Slot, t = (Model.spec (V := V)).proposal_time S.E s ∨ t = (Model.spec (V := V)).vote_time S.E s ∨
    t = (Model.spec (V := V)).support_cutoff S.E s ∨ t = (Model.spec (V := V)).view_freeze S.E s := by
  simp only [proposal_time_spec, vote_time_spec, support_cutoff_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).publicTime_iff

/-- The field `ActionRound_slotOf_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    confirmation time of slot `s` is in slot `s + 1`. -/
theorem spec_ActionRound_slotOf_confirmation_time : ∀ (E : Env V) (s : Slot), E.slotOf ((Model.spec (V := V)).confirmation_time E s) = s + 1 := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).ActionRound_slotOf_confirmation_time

/-- The field `slotOf_of_between'` of `ScheduleFacts` at `Model.spec`: every time `p` from the
    support cutoff of slot `s` to strictly before its view freeze is in slot `s`. -/
theorem spec_slotOf_of_between' : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : (Model.spec (V := V)).support_cutoff E s ≤ p) (hhi : p < (Model.spec (V := V)).view_freeze E s), E.slotOf p = s := by
  simp only [support_cutoff_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_of_between'

/-- The field `Optimistic_proposal_time_nonneg` of `ScheduleFacts` at `Model.spec`: every
    proposal time is non-negative. -/
theorem spec_Optimistic_proposal_time_nonneg : ∀ (E : Env V) (s : Slot), 0 ≤ (Model.spec (V := V)).proposal_time E s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Optimistic_proposal_time_nonneg

/-- The field `Optimistic_slotOf_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    confirmation time of slot `s` is in slot `s + 1`. -/
theorem spec_Optimistic_slotOf_confirmation_time : ∀ (E : Env V) (s : Slot), E.slotOf ((Model.spec (V := V)).confirmation_time E s) = s + 1 := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Optimistic_slotOf_confirmation_time

/-- The field `slotOf_of_between` of `ScheduleFacts` at `Model.spec`: every time `p` from the
    Goldfish vote time of slot `s` to strictly before its support cutoff is in slot `s`. -/
theorem spec_slotOf_of_between : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : (Model.spec (V := V)).vote_time E s ≤ p) (hhi : p < (Model.spec (V := V)).support_cutoff E s), E.slotOf p = s := by
  simp only [vote_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_of_between

/-- The field `slotOf_proposal_time` of `ScheduleFacts` at `Model.spec`: the proposal time of
    slot `s` is in slot `s`. -/
theorem spec_slotOf_proposal_time : ∀ (E : Env V) (s : Slot), E.slotOf ((Model.spec (V := V)).proposal_time E s) = s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_proposal_time

/-- The field `slotOf_support_cutoff` of `ScheduleFacts` at `Model.spec`: the support cutoff of
    slot `s` is in slot `s`. -/
theorem spec_slotOf_support_cutoff : ∀ (E : Env V) (s : Slot), E.slotOf ((Model.spec (V := V)).support_cutoff E s) = s := by
  simp only [support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_support_cutoff

/-- The field `slotOf_vote_time` of `ScheduleFacts` at `Model.spec`: the Goldfish vote time of
    slot `s` is in slot `s`. -/
theorem spec_slotOf_vote_time : ∀ (E : Env V) (s : Slot), E.slotOf ((Model.spec (V := V)).vote_time E s) = s := by
  simp only [vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_vote_time

/-- The field `support_cutoff_le_vote_time_succ` of `ScheduleFacts` at `Model.spec`: the
    support cutoff of slot `s` is at most the Goldfish vote time of slot `s + 1`. -/
theorem spec_support_cutoff_le_vote_time_succ : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s ≤ (Model.spec (V := V)).vote_time E (s + 1) := by
  simp only [vote_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_le_vote_time_succ

/-- The field `Optimistic_support_cutoff_lt_view_freeze` of `ScheduleFacts` at `Model.spec`:
    the support cutoff of slot `s` is strictly before the view freeze of slot `s`. -/
theorem spec_Optimistic_support_cutoff_lt_view_freeze : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s < (Model.spec (V := V)).view_freeze E s := by
  simp only [support_cutoff_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Optimistic_support_cutoff_lt_view_freeze

/-- The field `support_cutoff_ne_proposal_time` of `ScheduleFacts` at `Model.spec`: the support
    cutoff of slot `s` differs from its proposal time. -/
theorem spec_support_cutoff_ne_proposal_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s ≠ (Model.spec (V := V)).proposal_time E s := by
  simp only [proposal_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_ne_proposal_time

/-- The field `support_cutoff_ne_vote_time` of `ScheduleFacts` at `Model.spec`: the support
    cutoff of slot `s` differs from its Goldfish vote time. -/
theorem spec_support_cutoff_ne_vote_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s ≠ (Model.spec (V := V)).vote_time E s := by
  simp only [vote_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_ne_vote_time

/-- The field `vote_time_ne_proposal_time` of `ScheduleFacts` at `Model.spec`: the Goldfish
    vote time of slot `s` differs from its proposal time. -/
theorem spec_vote_time_ne_proposal_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).vote_time E s ≠ (Model.spec (V := V)).proposal_time E s := by
  simp only [proposal_time_spec, vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_ne_proposal_time

/-- The field `equivocates_mono` of `ScheduleFacts` at `Model.spec`: if `A ⊆ B` and `x`
    equivocates in `A`, then `x` equivocates in `B`. -/
theorem spec_equivocates_mono : ∀ {A B : Finset (GoldfishVote V)} (hAB : A ⊆ B) (x : V) (hA : (Model.spec (V := V)).equivocates A x = true), (Model.spec (V := V)).equivocates B x = true := by
  simp only [equivocates_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).equivocates_mono

/-- The field `proposal_time_le_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    proposal time of slot `s` is at most its confirmation time. -/
theorem spec_proposal_time_le_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).proposal_time E s ≤ (Model.spec (V := V)).confirmation_time E s := by
  simp only [proposal_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_le_confirmation_time

/-- The field `proposal_time_lt_vote_time` of `ScheduleFacts` at `Model.spec`: the proposal
    time of slot `s` is strictly before its Goldfish vote time. -/
theorem spec_proposal_time_lt_vote_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).proposal_time E s < (Model.spec (V := V)).vote_time E s := by
  simp only [proposal_time_spec, vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_lt_vote_time

/-- The field `proposal_time_mono` of `ScheduleFacts` at `Model.spec`: the proposal time is
    monotone in the slot. -/
theorem spec_proposal_time_mono : ∀ (E : Env V) {s s' : Slot} (h : s ≤ s'), (Model.spec (V := V)).proposal_time E s ≤ (Model.spec (V := V)).proposal_time E s' := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_mono

/-- The field `proposal_time_mono_local` of `ScheduleFacts` at `Model.spec`: the proposal time
    is monotone in the slot. -/
theorem spec_proposal_time_mono_local : ∀ (E : Env V) {s s' : Slot} (h : s ≤ s'), (Model.spec (V := V)).proposal_time E s ≤ (Model.spec (V := V)).proposal_time E s' := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_mono_local

/-- The field `proposal_time_pos_of_slot_pos` of `ScheduleFacts` at `Model.spec`: the proposal
    time of a slot `s > 0` is positive. -/
theorem spec_proposal_time_pos_of_slot_pos : ∀ (E : Env V) {s : Slot} (hs : 0 < s), 0 < (Model.spec (V := V)).proposal_time E s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_pos_of_slot_pos

/-- The field `proposal_time_slotOf_le` of `ScheduleFacts` at `Model.spec`: for `t ≥ 0`, the
    proposal time of the slot of `t` is at most `t`. -/
theorem spec_proposal_time_slotOf_le : ∀ (E : Env V) {t : Time} (ht : 0 ≤ t), (Model.spec (V := V)).proposal_time E (E.slotOf t) ≤ t := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_slotOf_le

/-- The field `proposal_time_succ_lt_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    proposal time of slot `s + 1` is strictly before the confirmation time of slot `s`. -/
theorem spec_proposal_time_succ_lt_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).proposal_time E (s + 1) < (Model.spec (V := V)).confirmation_time E s := by
  simp only [proposal_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_succ_lt_confirmation_time

/-- The field `slotOf_of_proposal_before_confirmation` of `ScheduleFacts` at `Model.spec`:
    every time `p` from the proposal time of slot `s` to strictly before its confirmation time is in
    slot `s` or `s + 1`. -/
theorem spec_slotOf_of_proposal_before_confirmation : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : (Model.spec (V := V)).proposal_time E s ≤ p) (hhi : p < (Model.spec (V := V)).confirmation_time E s), E.slotOf p = s ∨ E.slotOf p = s + 1 := by
  simp only [proposal_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_of_proposal_before_confirmation

/-- The field `slotOf_of_proposal_before_freeze` of `ScheduleFacts` at `Model.spec`: every time
    `p` from the proposal time of slot `s` to strictly before its view freeze is in slot `s`. -/
theorem spec_slotOf_of_proposal_before_freeze : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : (Model.spec (V := V)).proposal_time E s ≤ p) (hhi : p < (Model.spec (V := V)).view_freeze E s), E.slotOf p = s := by
  simp only [proposal_time_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_of_proposal_before_freeze

/-- The field `slot_le_slotOf_of_proposal_time_le` of `ScheduleFacts` at `Model.spec`: if the
    proposal time of slot `s` is at most `t`, then `s` is at most the slot of `t`. -/
theorem spec_slot_le_slotOf_of_proposal_time_le : ∀ (E : Env V) {s : Slot} {t : Time} (h : (Model.spec (V := V)).proposal_time E s ≤ t), s ≤ E.slotOf t := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slot_le_slotOf_of_proposal_time_le

/-- The field `Protocol_support_cutoff_le_confirmation_time` of `ScheduleFacts` at
    `Model.spec`: the support cutoff of slot `s` is at most its confirmation time. -/
theorem spec_Protocol_support_cutoff_le_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s ≤ (Model.spec (V := V)).confirmation_time E s := by
  simp only [support_cutoff_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Protocol_support_cutoff_le_confirmation_time

/-- The field `support_cutoff_le_proposal_time_succ` of `ScheduleFacts` at `Model.spec`: the
    support cutoff of slot `s` is at most the proposal time of slot `s + 1`. -/
theorem spec_support_cutoff_le_proposal_time_succ : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s ≤ (Model.spec (V := V)).proposal_time E (s + 1) := by
  simp only [proposal_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_le_proposal_time_succ

/-- The field `support_cutoff_lt_proposal_time_succ` of `ScheduleFacts` at `Model.spec`: the
    support cutoff of slot `s` is strictly before the proposal time of slot `s + 1`. -/
theorem spec_support_cutoff_lt_proposal_time_succ : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s < (Model.spec (V := V)).proposal_time E (s + 1) := by
  simp only [proposal_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_lt_proposal_time_succ

/-- The field `view_freeze_add_delta_lt_confirmation_time` of `ScheduleFacts` at `Model.spec`:
    the view freeze of slot `s` plus `E.Δ` is strictly before its confirmation time. -/
theorem spec_view_freeze_add_delta_lt_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).view_freeze E s + E.Δ < (Model.spec (V := V)).confirmation_time E s := by
  simp only [view_freeze_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).view_freeze_add_delta_lt_confirmation_time

/-- The field `view_freeze_lt_confirmation_time` of `ScheduleFacts` at `Model.spec`: the view
    freeze of slot `s` is strictly before its confirmation time. -/
theorem spec_view_freeze_lt_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).view_freeze E s < (Model.spec (V := V)).confirmation_time E s := by
  simp only [view_freeze_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).view_freeze_lt_confirmation_time

/-- The field `view_freeze_lt_vote_time_succ` of `ScheduleFacts` at `Model.spec`: the view
    freeze of slot `s` is strictly before the Goldfish vote time of slot `s + 1`. -/
theorem spec_view_freeze_lt_vote_time_succ : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).view_freeze E s < (Model.spec (V := V)).vote_time E (s + 1) := by
  simp only [vote_time_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).view_freeze_lt_vote_time_succ

/-- The field `Protocol_vote_time_le_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    Goldfish vote time of slot `s` is at most its confirmation time. -/
theorem spec_Protocol_vote_time_le_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).vote_time E s ≤ (Model.spec (V := V)).confirmation_time E s := by
  simp only [vote_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Protocol_vote_time_le_confirmation_time

/-- The field `vote_time_mono_slots` of `ScheduleFacts` at `Model.spec`: the Goldfish vote time
    is monotone in the slot. -/
theorem spec_vote_time_mono_slots : ∀ (E : Env V) {a b : Slot} (hab : a ≤ b), (Model.spec (V := V)).vote_time E a ≤ (Model.spec (V := V)).vote_time E b := by
  simp only [vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_mono_slots

/-- The field `confirmation_time_eq_of_delta_eq` of `ScheduleFacts` at `Model.spec`: two
    environments with the same delay `Δ` give every slot the same confirmation time. -/
theorem spec_confirmation_time_eq_of_delta_eq : ∀ {E E' : Env V} (h : E.Δ = E'.Δ) (s : Slot), (Model.spec (V := V)).confirmation_time E s = (Model.spec (V := V)).confirmation_time E' s := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).confirmation_time_eq_of_delta_eq

/-- The field `confirmation_time_mono` of `ScheduleFacts` at `Model.spec`: the confirmation
    time is monotone in the slot. -/
theorem spec_confirmation_time_mono : ∀ (S : Setup V) {s s' : Slot} (h : s ≤ s'), (Model.spec (V := V)).confirmation_time S.E s ≤ (Model.spec (V := V)).confirmation_time S.E s' := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).confirmation_time_mono

/-- The field `confirmation_time_mono_l78` of `ScheduleFacts` at `Model.spec`: the confirmation
    time is monotone in the slot. -/
theorem spec_confirmation_time_mono_l78 : ∀ (S : Setup V) {s s' : Slot} (h : s ≤ s'), (Model.spec (V := V)).confirmation_time S.E s ≤ (Model.spec (V := V)).confirmation_time S.E s' := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).confirmation_time_mono_l78

/-- The field `equivocates_eq_false_of_card_le_one` of `ScheduleFacts` at `Model.spec`: if
    `votes` holds at most one vote of `w`, then `w` does not equivocate in `votes`. -/
theorem spec_equivocates_eq_false_of_card_le_one : ∀ {votes : Finset (GoldfishVote V)} {w : V} (h : ((Model.spec (V := V)).votes_by votes w).card ≤ 1), (Model.spec (V := V)).equivocates votes w = false := by
  simp only [votes_by_spec, equivocates_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).equivocates_eq_false_of_card_le_one

/-- The field `equivocates_eq_true_iff` of `ScheduleFacts` at `Model.spec`: `w` equivocates in
    `votes` exactly when `votes` holds two different votes signed by `w`. -/
theorem spec_equivocates_eq_true_iff : ∀ (votes : Finset (GoldfishVote V)) (w : V), (Model.spec (V := V)).equivocates votes w = true ↔
    ∃ u ∈ votes, ∃ u' ∈ votes, u ≠ u' ∧ u.val_index = w ∧ u'.val_index = w := by
  simp only [equivocates_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).equivocates_eq_true_iff

/-- The field `equivocates_mono_of_subset` of `ScheduleFacts` at `Model.spec`: if
    `votes ⊆ votes'` and `w` equivocates in `votes`, then `w` equivocates in `votes'`. -/
theorem spec_equivocates_mono_of_subset : ∀ {votes votes' : Finset (GoldfishVote V)} (hsub : votes ⊆ votes') {w : V} (h : (Model.spec (V := V)).equivocates votes w = true), (Model.spec (V := V)).equivocates votes' w = true := by
  simp only [equivocates_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).equivocates_mono_of_subset

/-- The field `exists_confirmation_time_ge` of `ScheduleFacts` at `Model.spec`: for every time
    `t` some slot has a confirmation time at least `t`. -/
theorem spec_exists_confirmation_time_ge : ∀ (S : Setup V) (t : Time), ∃ s : Slot, t ≤ (Model.spec (V := V)).confirmation_time S.E s := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).exists_confirmation_time_ge

/-- The field `mem_votes_by_iff` of `ScheduleFacts` at `Model.spec`: `u` is among the votes of
    `votes` cast by `v` exactly when `u` is in `votes` and its validator index is `v`. -/
theorem spec_mem_votes_by_iff : ∀ (votes : Finset (GoldfishVote V)) (v : V) (u : GoldfishVote V), u ∈ (Model.spec (V := V)).votes_by votes v ↔ u ∈ votes ∧ u.val_index = v := by
  simp only [votes_by_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).mem_votes_by_iff

/-- The field `participates_eq_true_iff` of `ScheduleFacts` at `Model.spec`: `w` participates
    in `votes` exactly when `votes` holds a vote signed by `w`. -/
theorem spec_participates_eq_true_iff : ∀ (votes : Finset (GoldfishVote V)) (w : V), (Model.spec (V := V)).participates votes w = true ↔ ∃ u ∈ votes, u.val_index = w := by
  simp only [participates_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).participates_eq_true_iff

/-- The field `participates_of_equivocates` of `ScheduleFacts` at `Model.spec`: if `w`
    equivocates in `votes`, then `w` participates in `votes`. -/
theorem spec_participates_of_equivocates : ∀ {votes : Finset (GoldfishVote V)} {w : V} (h : (Model.spec (V := V)).equivocates votes w = true), (Model.spec (V := V)).participates votes w = true := by
  simp only [equivocates_spec, participates_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).participates_of_equivocates

/-- The field `proposal_time_emod_delta_inclX` of `ScheduleFacts` at `Model.spec`: the proposal
    time of slot `s` is a multiple of `E.Δ`. -/
theorem spec_proposal_time_emod_delta_inclX : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).proposal_time E s % E.Δ = 0 := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_emod_delta_inclX

/-- The field `proposal_time_eq_of_delta_eq` of `ScheduleFacts` at `Model.spec`: two
    environments with the same delay `Δ` give every slot the same proposal time. -/
theorem spec_proposal_time_eq_of_delta_eq : ∀ {E E' : Env V} (h : E.Δ = E'.Δ) (s : Slot), (Model.spec (V := V)).proposal_time E s = (Model.spec (V := V)).proposal_time E' s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).proposal_time_eq_of_delta_eq

/-- The field `Sts_proposal_time_nonneg` of `ScheduleFacts` at `Model.spec`: every proposal
    time is non-negative. -/
theorem spec_Sts_proposal_time_nonneg : ∀ (S : Setup V) (s : Slot), (0 : Int) ≤ (Model.spec (V := V)).proposal_time S.E s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Sts_proposal_time_nonneg

/-- The field `slot_pos_of_proposal_time_pos_inclX` of `ScheduleFacts` at `Model.spec`: if the
    proposal time of slot `s` is positive, then `0 < s`. -/
theorem spec_slot_pos_of_proposal_time_pos_inclX : ∀ (E : Env V) {s : Slot} (h : 0 < (Model.spec (V := V)).proposal_time E s), 0 < s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slot_pos_of_proposal_time_pos_inclX

/-- The field `support_cutoff_emod_delta` of `ScheduleFacts` at `Model.spec`: the support
    cutoff of slot `s` is a multiple of `S.E.Δ`. -/
theorem spec_support_cutoff_emod_delta : ∀ (S : Setup V) (s : Slot), (Model.spec (V := V)).support_cutoff S.E s % S.E.Δ = 0 := by
  simp only [support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_emod_delta

/-- The field `Sts_support_cutoff_le_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    support cutoff of slot `s` is at most its confirmation time. -/
theorem spec_Sts_support_cutoff_le_confirmation_time : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s ≤ (Model.spec (V := V)).confirmation_time E s := by
  simp only [support_cutoff_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Sts_support_cutoff_le_confirmation_time

/-- The field `Sts_support_cutoff_lt_view_freeze` of `ScheduleFacts` at `Model.spec`: the
    support cutoff of slot `s` is strictly before its view freeze. -/
theorem spec_Sts_support_cutoff_lt_view_freeze : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).support_cutoff E s < (Model.spec (V := V)).view_freeze E s := by
  simp only [support_cutoff_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Sts_support_cutoff_lt_view_freeze

/-- The field `support_cutoff_pos` of `ScheduleFacts` at `Model.spec`: every support cutoff is
    positive. -/
theorem spec_support_cutoff_pos : ∀ (S : Setup V) (s : Slot), 0 < (Model.spec (V := V)).support_cutoff S.E s := by
  simp only [support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_pos

/-- The field `voteTime_lt_nextProposal_l86d` of `ScheduleFacts` at `Model.spec`:
    `vote_time s < proposal_time (s + 1)`. -/
theorem spec_voteTime_lt_nextProposal_l86d : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).vote_time E s < (Model.spec (V := V)).proposal_time E (s + 1) := by
  simp only [proposal_time_spec, vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).voteTime_lt_nextProposal_l86d

/-- The field `voteWindow_prev_inPhase` of `ScheduleFacts` at `Model.spec`: if
    `tGAT + 8RΔ ≤ tE' ≤ slotStart s < tE` and `1 ≤ s`, the window
    `[slotStart (s − 1) + Δ − wVote, slotStart (s − 1) + Δ]` lies inside `[tGAT, tE]`, and its end
    is at most both `slotStart s + Δ` and `confirmation_time (s − 1)`. -/
theorem spec_voteWindow_prev_inPhase : ∀ (S : Setup V) (tGAT tE tE' : Int) {s : Slot} (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hs1 : 1 ≤ s) (hs' : tE' ≤ slotStart S.E.Δ s) (hsE : slotStart S.E.Δ s < tE), tGAT ≤ slotStart S.E.Δ (s - 1) + S.E.Δ - wVote S ∧
    slotStart S.E.Δ (s - 1) + S.E.Δ ≤ tE ∧
    slotStart S.E.Δ (s - 1) + S.E.Δ ≤ slotStart S.E.Δ s + S.E.Δ ∧
    slotStart S.E.Δ (s - 1) + S.E.Δ ≤ (Model.spec (V := V)).confirmation_time S.E (s - 1) := by
  simp only [confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).voteWindow_prev_inPhase

/-- The field `vote_time_add_delta_le_confirmation_time` of `ScheduleFacts` at `Model.spec`: a
    slot's Goldfish vote time plus one delay is at most its confirmation time. -/
theorem spec_vote_time_add_delta_le_confirmation_time : ∀ (S : Setup V) (s : Slot), (Model.spec (V := V)).vote_time S.E s + S.E.Δ ≤ (Model.spec (V := V)).confirmation_time S.E s := by
  simp only [vote_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_add_delta_le_confirmation_time

/-- The field `vote_time_emod_delta` of `ScheduleFacts` at `Model.spec`: the Goldfish vote time
    of slot `s` is a multiple of `S.E.Δ`. -/
theorem spec_vote_time_emod_delta : ∀ (S : Setup V) (s : Slot), (Model.spec (V := V)).vote_time S.E s % S.E.Δ = 0 := by
  simp only [vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_emod_delta

/-- The field `Sts_vote_time_le_confirmation_time` of `ScheduleFacts` at `Model.spec`: the
    Goldfish vote time of slot `s` is at most its confirmation time. -/
theorem spec_Sts_vote_time_le_confirmation_time : ∀ (S : Setup V) (s : Slot), (Model.spec (V := V)).vote_time S.E s ≤ (Model.spec (V := V)).confirmation_time S.E s := by
  simp only [vote_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).Sts_vote_time_le_confirmation_time

/-- The field `vote_time_mono` of `ScheduleFacts` at `Model.spec`: the Goldfish vote time is
    monotone in the slot. -/
theorem spec_vote_time_mono : ∀ (E : Env V) {s s' : Slot} (h : s ≤ s'), (Model.spec (V := V)).vote_time E s ≤ (Model.spec (V := V)).vote_time E s' := by
  simp only [vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_mono

/-- The field `vote_time_pos` of `ScheduleFacts` at `Model.spec`: the Goldfish vote time of a
    slot `s > 0` is positive. -/
theorem spec_vote_time_pos : ∀ (S : Setup V) {s : Slot} (hs : 0 < s), 0 < (Model.spec (V := V)).vote_time S.E s := by
  simp only [vote_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_pos

/-- The field `support_cutoff_lt_vote_time_imp_lt_proposal_time` of `ScheduleFacts` at
    `Model.spec`: if the support cutoff of slot `k` is strictly before the Goldfish vote time
    of slot `s`, it is strictly before the proposal time of slot `s`. -/
theorem spec_support_cutoff_lt_vote_time_imp_lt_proposal_time : ∀ (E : Env V) {k s : Slot} (h : (Model.spec (V := V)).support_cutoff E k < (Model.spec (V := V)).vote_time E s), (Model.spec (V := V)).support_cutoff E k < (Model.spec (V := V)).proposal_time E s := by
  simp only [proposal_time_spec, vote_time_spec, support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_lt_vote_time_imp_lt_proposal_time

/-- The field `slotOf_of_proposal_before_next_proposal` of `ScheduleFacts` at `Model.spec`:
    every time `p` from the proposal time of slot `s` to strictly before that of slot `s + 1` is in
    slot `s`. -/
theorem spec_slotOf_of_proposal_before_next_proposal : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : (Model.spec (V := V)).proposal_time E s ≤ p) (hhi : p < (Model.spec (V := V)).proposal_time E (s + 1)), E.slotOf p = s := by
  simp only [proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slotOf_of_proposal_before_next_proposal

/-- The field `confirmationTime_lt_proposalTime_of_two_le` of `ScheduleFacts` at `Model.spec`:
    if `s + 2 ≤ s'`, the confirmation time of slot `s` is strictly before the proposal time of slot
    `s'`. -/
theorem spec_confirmationTime_lt_proposalTime_of_two_le : ∀ (E : Env V) {s s' : Slot} (h : s + 2 ≤ s'), (Model.spec (V := V)).confirmation_time E s < (Model.spec (V := V)).proposal_time E s' := by
  simp only [proposal_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).confirmationTime_lt_proposalTime_of_two_le

/-- The field `on_goldfish_vote_insert` of `ScheduleFacts` at `Model.specBase`: if `u` is of a
    slot from `st.s - 1` to `st.s`, not yet among `st`'s votes of its slot, and its validator does
    not equivocate in `st.pool u.slot`, then `on_goldfish_vote st u` appends `u` to its slot's
    votes, stamps it with `st.t`, and keeps the other votes, the other stamps and the time. -/
theorem specBase_on_goldfish_vote_insert : ∀ (st : (Model.specBase (V := V)).S) (u : GoldfishVote V) (h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot)) (h2 : ¬ (Model.specBase (V := V)).equivocates (st.pool u.slot) u.val_index = true),
    ((Model.specBase (V := V)).on_goldfish_vote st u).gf_votes =
    (fun k => if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k) ∧
    ((Model.specBase (V := V)).on_goldfish_vote st u).timestamp_vote =
    (fun x => if x = u then some (st.t : Stamp) else st.timestamp_vote x) ∧
    ((Model.specBase (V := V)).on_goldfish_vote st u).t = st.t := by
  intro st u h1 h2
  have hpool : (Model.specBase (V := V)).store_pool st u.slot =
      Protocol.Store.pool st.toProof u.slot := by
    show (Spec.Store.pool st u.slot).map _ = _
    rw [toProof_store_pool]
  have h2' : ¬ Protocol.equivocates (Protocol.Store.pool st.toProof u.slot) u.val_index = true := by
    rw [← hpool]
    rw [equivocates_spec_base] at h2
    exact h2
  have hup := (Model.vocabulary_facts_schedule (V := V)).on_goldfish_vote_insert st.toProof u h1 h2'
  show (Spec.Protocol.on_goldfish_vote st _).toProof.gf_votes = _ ∧
    (Spec.Protocol.on_goldfish_vote st _).toProof.timestamp_vote = _ ∧
    (Spec.Protocol.on_goldfish_vote st _).toProof.t = _
  rw [← toProof_on_goldfish_vote, Spec.GoldfishVote.toProof_toSpec]
  exact hup

/-- The field `on_goldfish_vote_insert` of `ScheduleFacts` at `Model.spec`: if `u` is of a slot
    from `st.s - 1` to `st.s`, not yet among `st`'s votes of its slot, and its validator does not
    equivocate in `st.pool u.slot`, then `on_goldfish_vote st u` appends `u` to its slot's votes,
    stamps it with `st.t`, and keeps the other votes, the other stamps and the time. -/
theorem spec_on_goldfish_vote_insert : ∀ (st : (Model.spec (V := V)).S) (u : GoldfishVote V) (h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot)) (h2 : ¬ (Model.spec (V := V)).equivocates (st.pool u.slot) u.val_index = true),
    ((Model.spec (V := V)).on_goldfish_vote st u).gf_votes =
    (fun k => if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k) ∧
    ((Model.spec (V := V)).on_goldfish_vote st u).timestamp_vote =
    (fun x => if x = u then some (st.t : Stamp) else st.timestamp_vote x) ∧
    ((Model.spec (V := V)).on_goldfish_vote st u).t = st.t :=
  fun st u h1 h2 => specBase_on_goldfish_vote_insert st.val u h1 h2

/-- The field `action_round_le_of_lt_proposal` of `ScheduleFacts` at `Model.spec`: if the
    action time of round `r` is strictly before the proposal time of slot `s`, then `r` is at most
    the round of slot `s`. -/
theorem spec_action_round_le_of_lt_proposal : ∀ (S : Setup V) {r : Round} {s : Slot} (hlt : (Model.spec (V := V)).a S.hc S.E.Δ r < (Model.spec (V := V)).proposal_time S.E s), r ≤ (Model.spec (V := V)).round_of S.hc s := by
  simp only [proposal_time_spec, round_of_spec, a_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).action_round_le_of_lt_proposal

/-- The field `support_cutoff_mono` of `ScheduleFacts` at `Model.spec`: the support cutoff is
    monotone in the slot. -/
theorem spec_support_cutoff_mono : ∀ (E : Env V) {a b : Slot}, a ≤ b → (Model.spec (V := V)).support_cutoff E a ≤ (Model.spec (V := V)).support_cutoff E b := by
  simp only [support_cutoff_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).support_cutoff_mono

/-- The field `view_freeze_add_delta_le_proposal_time_succ` of `ScheduleFacts` at `Model.spec`:
    one delay after slot `s`'s view freeze is at most slot `s + 1`'s proposal time. -/
theorem spec_view_freeze_add_delta_le_proposal_time_succ : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).view_freeze E s + E.Δ ≤ (Model.spec (V := V)).proposal_time E (s + 1) := by
  simp only [view_freeze_spec, proposal_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).view_freeze_add_delta_le_proposal_time_succ

/-- The field `vote_time_le_view_freeze` of `ScheduleFacts` at `Model.spec`: slot `s`'s
    Goldfish vote time is at most its view freeze. -/
theorem spec_vote_time_le_view_freeze : ∀ (E : Env V) (s : Slot), (Model.spec (V := V)).vote_time E s ≤ (Model.spec (V := V)).view_freeze E s := by
  simp only [vote_time_spec, view_freeze_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).vote_time_le_view_freeze

/-- The field `slot_instants_l55` of `ScheduleFacts` at `Model.spec`: from slot `s`'s proposal
    time, the vote time is `Δ` later, the support cutoff `2Δ`, the view freeze `3Δ`, the proposal
    time of `s + 1` `4Δ`, the vote time of `s + 1` `5Δ`, and the confirmation time of `s` `6Δ`. -/
theorem spec_slot_instants_l55 : ∀ (E : Env V) (s : Slot),
    (Model.spec (V := V)).vote_time E s = (Model.spec (V := V)).proposal_time E s + E.Δ ∧
      (Model.spec (V := V)).support_cutoff E s = (Model.spec (V := V)).proposal_time E s + 2 * E.Δ ∧
      (Model.spec (V := V)).view_freeze E s = (Model.spec (V := V)).proposal_time E s + 3 * E.Δ ∧
      (Model.spec (V := V)).proposal_time E (s + 1) = (Model.spec (V := V)).proposal_time E s + 4 * E.Δ ∧
      (Model.spec (V := V)).vote_time E (s + 1) = (Model.spec (V := V)).proposal_time E s + 5 * E.Δ ∧
      (Model.spec (V := V)).confirmation_time E s = (Model.spec (V := V)).proposal_time E s + 6 * E.Δ := by
  simp only [vote_time_spec, support_cutoff_spec, view_freeze_spec,
    proposal_time_spec, confirmation_time_spec]
  exact (Model.vocabulary_facts_schedule (V := V)).slot_instants_l55

/-- The field `proposal_wake_start_lt_proposal_time` of `ScheduleFacts` at `Model.spec`: the
    window throughout which slot `s`'s proposer must be awake starts strictly before slot `s`'s
    proposal time. -/
theorem spec_proposal_wake_start_lt_proposal_time : ∀ (S : Setup V) (s : Slot), (Model.spec (V := V)).proposal_wake_start S s < (Model.spec (V := V)).proposal_time S.E s := by
  intro S s
  rw [proposal_time_spec]
  show Spec.grade1_window_start (Spec.Config.toSpec S.E S.hc S.cfg)
      ((Spec.Config.toSpec S.E S.hc S.cfg).round_of s) < (Model.vocabulary (V := V)).proposal_time S.E s
  rw [show (Model.vocabulary (V := V)).proposal_time S.E s
      = (Spec.Config.toSpec S.E S.hc S.cfg).proposal_time s from toProof_proposal_time S.E S.hc S.cfg s]
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hle : s / S.hc.R * S.hc.R ≤ s := Nat.div_mul_le_self s S.hc.R
  have hle' : ((s / S.hc.R * S.hc.R : Nat) : Int) ≤ (s : Int) := by exact_mod_cast hle
  simp only [Spec.grade1_window_start, Spec.Config.early,
    Spec.Config.opening, Spec.Config.proposal_time,
    Spec.Config.round_of, Spec.Protocol.Phase.earlyOffset, Spec.Config.toSpec]
  simp only [reduceCtorEq, if_false, if_true]
  nlinarith

/-- The field `proposal_wake_start_le_proposal_time` of `ScheduleFacts` at `Model.spec`: the
    window throughout which slot `s`'s proposer must be awake starts at or before slot `s`'s
    proposal time. -/
theorem spec_proposal_wake_start_le_proposal_time : ∀ (S : Setup V) (s : Slot), (Model.spec (V := V)).proposal_wake_start S s ≤ (Model.spec (V := V)).proposal_time S.E s :=
  fun S s => le_of_lt (spec_proposal_wake_start_lt_proposal_time S s)


/-- The field `mem_voter_support_view_of_pool` of `ScheduleFacts` at `Model.spec`: if `u` is in
    `gs.pool s`, stamped strictly before the view freeze of slot `s`, and its head resolves among
    `gs`'s blocks to a block of slot at most `u`'s, stamped strictly before that view freeze, then
    `u` is in every outcome of `voter_support_view E gs (s + 1)`. -/
theorem spec_mem_voter_support_view_of_pool : ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V} (hu : u ∈ gs.pool s) {τ : Stamp} (hτ : gs.timestamp_vote u = some τ) (hlt : τ < (((Model.spec (V := V)).view_freeze E s : Int) : Stamp)) {X : Block V} (hX : Block.find? gs.T u.head = some X) (hXs : X.slot ≤ u.slot) {σ : Stamp} (hσ : gs.timestamp_block X = some σ) (hσlt : σ < (((Model.spec (V := V)).view_freeze E s : Int) : Stamp))
    (W : Finset (GoldfishVote V)) (hW : (Model.spec (V := V)).voter_support_view E gs (s + 1) ⇢ W),
    u ∈ W := by
  intro E gs s u hu τ hτ hlt X hX hXs σ hσ hσlt W hW
  rw [ForkChoiceImages.spec_voter_support_view_eq] at hW
  rw [ForkChoiceImages.spec_view_freeze_eq] at hlt hσlt
  change u ∈ (Model.spec (V := V)).gs_pool gs s at hu
  rw [ForkChoiceImages.spec_gs_pool_eq] at hu
  exact (Model.vocabulary_facts_schedule (V := V)).mem_voter_support_view_of_pool E _ s hu hτ hlt
    hX hXs hσ hσlt W hW

end SpecRecord.ScheduleFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.spec` satisfies `ScheduleRunFacts`, which has no field. -/
theorem Model.spec_runFacts_schedule : ScheduleRunFacts (Model.spec (V := V)) where

end DecoupledConsensusModel.Sts.Record
