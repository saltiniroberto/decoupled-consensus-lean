import Model.Record.Wiring
import Model.Sts.Spec2Claims.Claim13be
import Model.Record.ModelSpellings
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_early_mk
import Proofs.Vocabulary.Protocol.Handlers.RawRelay
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Protocol.Handlers.Admission
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade
import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
import Proofs.Vocabulary.ModelProperties.NamedStore_commitBlock
import Proofs.Vocabulary.ModelProperties.on_block_checked_using
import Proofs.Vocabulary.ModelProperties.Block_prec
import Proofs.Vocabulary.ModelProperties.Block_parent
import Proofs.Vocabulary.ModelProperties.NamedBlock_erase
import Proofs.Vocabulary.ModelProperties.on_block_using
import Proofs.Vocabulary.ModelProperties.update_finality
import Proofs.Vocabulary.ModelProperties.viable_tree
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge

/-!
# Facts of the slot schedule

`ScheduleFacts` holds the facts a model `M` provides about its slot instants and about `votes_by`,
`equivocates` and `participates`. `ScheduleRunFacts`, for facts about runs, has no field.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Execution (Setup)
open Internal
open Execution
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Internal.NamedRecoveryRead
open Protocol
open Protocol (Record)
open DecoupledConsensusModel.Protocol
open Proofs.Optimistic
open Protocol (derive_named)
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades

/-- The facts about the slot instants of a model `M` and about its `votes_by`, `equivocates` and
    `participates`. -/
structure ScheduleFacts (M : Model V) : Prop where
  /-- The support cutoffs grow with the slot. -/
  support_cutoff_mono : ∀ (E : Env V) {a b : Slot}, a ≤ b →
    M.support_cutoff E a ≤ M.support_cutoff E b
  /-- The round of the slot of round `r`'s action instant is `r`. -/
  round_of_slotOf_a : ∀ (S : Setup V) (r : Round), M.round_of S.hc (S.E.slotOf (M.a S.hc S.E.Δ r)) = r
  /-- The confirmation instant of slot `s` is the start of slot `s` plus `6Δ`. -/
  slotStart_add_six_delta_eq_confirmation_time : ∀ (E : Env V) (s : Slot),
    slotStart E.Δ s + 6 * E.Δ = M.confirmation_time E s
  /-- The Goldfish vote instant of slot `s` is the start of slot `s` plus `Δ`. -/
  slotStart_add_delta_eq_vote_time : ∀ (E : Env V) (s : Slot),
    slotStart E.Δ s + E.Δ = M.vote_time E s
  /-- The Goldfish vote instant of slot `s + 1`, plus one delay, is at most the confirmation instant
      of slot `s`. -/
  vote_time_succ_add_delta_le_confirmation_time : ∀ (E : Env V) (s : Slot),
    M.vote_time E (s + 1) + E.Δ ≤ M.confirmation_time E s
  /-- One delay after round `r`'s action instant is the view freeze of the slot after round `r`'s
      opening slot. -/
  a_add_delta_eq_view_freeze : ∀ (S : Setup V) (r : Round), M.a S.hc S.E.Δ r + S.E.Δ = M.view_freeze S.E (M.opening_slot S.hc r + 1)
  /-- The start of round `r`'s opening slot is that slot's proposal instant. -/
  Γ_0_eq_proposal_time : ∀ (hc : HealConfig) (E : Env V) (r : Round), slotStart E.Δ (M.opening_slot hc r) = M.proposal_time E (M.opening_slot hc r)
  /-- One delay after the start of round `r`'s opening slot is that slot's Goldfish vote instant. -/
  Γ_1_eq_vote_time : ∀ (hc : HealConfig) (E : Env V) (r : Round), slotStart E.Δ (M.opening_slot hc r) + E.Δ = M.vote_time E (M.opening_slot hc r)
  /-- The action instant of round `r` is the confirmation instant of round `r`'s opening slot. -/
  a_eq_confirmation_time : ∀ (hc : HealConfig) (E : Env V) (r : Round), M.a hc E.Δ r = M.confirmation_time E (M.opening_slot hc r)
  /-- The confirmation instant of slot `s` is the support cutoff of slot `s + 1`. -/
  confirmation_time_eq_support_cutoff_succ : ∀ (E : Env V) (s : Slot), M.confirmation_time E s = M.support_cutoff E (s + 1)
  /-- An instant is a public time of `S` exactly when it is the proposal instant, the Goldfish vote
      instant, the support cutoff or the view freeze of some slot. -/
  publicTime_iff : ∀ (S : Setup V) (t : Time), PublicTime S t ↔
    ∃ s : Slot, t = M.proposal_time S.E s ∨ t = M.vote_time S.E s ∨
    t = M.support_cutoff S.E s ∨ t = M.view_freeze S.E s
  /-- The confirmation instant of slot `s` lies in slot `s + 1`. -/
  ActionRound_slotOf_confirmation_time : ∀ (E : Env V) (s : Slot), E.slotOf (M.confirmation_time E s) = s + 1
  /-- Every instant from the support cutoff of slot `s` to strictly before its view freeze lies in
      slot `s`. -/
  slotOf_of_between' : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : M.support_cutoff E s ≤ p) (hhi : p < M.view_freeze E s), E.slotOf p = s
  /-- The proposal instant of every slot is nonnegative. -/
  Optimistic_proposal_time_nonneg : ∀ (E : Env V) (s : Slot), 0 ≤ M.proposal_time E s
  /-- The confirmation instant of slot `s` lies in slot `s + 1`. -/
  Optimistic_slotOf_confirmation_time : ∀ (E : Env V) (s : Slot), E.slotOf (M.confirmation_time E s) = s + 1
  /-- Every instant from the Goldfish vote instant of slot `s` to strictly before its support cutoff
      lies in slot `s`. -/
  slotOf_of_between : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : M.vote_time E s ≤ p) (hhi : p < M.support_cutoff E s), E.slotOf p = s
  /-- The proposal instant of slot `s` lies in slot `s`. -/
  slotOf_proposal_time : ∀ (E : Env V) (s : Slot), E.slotOf (M.proposal_time E s) = s
  /-- The support cutoff of slot `s` lies in slot `s`. -/
  slotOf_support_cutoff : ∀ (E : Env V) (s : Slot), E.slotOf (M.support_cutoff E s) = s
  /-- The Goldfish vote instant of slot `s` lies in slot `s`. -/
  slotOf_vote_time : ∀ (E : Env V) (s : Slot), E.slotOf (M.vote_time E s) = s
  /-- The support cutoff of slot `s` is at or before the Goldfish vote instant of slot `s + 1`. -/
  support_cutoff_le_vote_time_succ : ∀ (E : Env V) (s : Slot), M.support_cutoff E s ≤ M.vote_time E (s + 1)
  /-- The support cutoff of slot `s` is strictly before its view freeze. -/
  Optimistic_support_cutoff_lt_view_freeze : ∀ (E : Env V) (s : Slot), M.support_cutoff E s < M.view_freeze E s
  /-- The support cutoff of slot `s` differs from its proposal instant. -/
  support_cutoff_ne_proposal_time : ∀ (E : Env V) (s : Slot), M.support_cutoff E s ≠ M.proposal_time E s
  /-- The support cutoff of slot `s` differs from its Goldfish vote instant. -/
  support_cutoff_ne_vote_time : ∀ (E : Env V) (s : Slot), M.support_cutoff E s ≠ M.vote_time E s
  /-- The Goldfish vote instant of slot `s` differs from its proposal instant. -/
  vote_time_ne_proposal_time : ∀ (E : Env V) (s : Slot), M.vote_time E s ≠ M.proposal_time E s
  /-- If the vote set `A` is contained in `B` and `x` equivocates in `A`, then `x` equivocates in
      `B`. -/
  equivocates_mono : ∀ {A B : Finset (GoldfishVote V)} (hAB : A ⊆ B) (x : V) (hA : M.equivocates A x = true), M.equivocates B x = true
  /-- The proposal instant of slot `s` is at or before its confirmation instant. -/
  proposal_time_le_confirmation_time : ∀ (E : Env V) (s : Slot), M.proposal_time E s ≤ M.confirmation_time E s
  /-- The proposal instant of slot `s` is strictly before its Goldfish vote instant. -/
  proposal_time_lt_vote_time : ∀ (E : Env V) (s : Slot), M.proposal_time E s < M.vote_time E s
  /-- The proposal instants grow with the slot. -/
  proposal_time_mono : ∀ (E : Env V) {s s' : Slot} (h : s ≤ s'), M.proposal_time E s ≤ M.proposal_time E s'
  /-- The proposal instants grow with the slot. -/
  proposal_time_mono_local : ∀ (E : Env V) {s s' : Slot} (h : s ≤ s'), M.proposal_time E s ≤ M.proposal_time E s'
  /-- The proposal instant of a positive slot is strictly after `0`. -/
  proposal_time_pos_of_slot_pos : ∀ (E : Env V) {s : Slot} (hs : 0 < s), 0 < M.proposal_time E s
  /-- For every nonnegative instant `t`, the proposal instant of the slot containing `t` is at or
      before `t`. -/
  proposal_time_slotOf_le : ∀ (E : Env V) {t : Time} (ht : 0 ≤ t), M.proposal_time E (E.slotOf t) ≤ t
  /-- The proposal instant of slot `s + 1` is strictly before the confirmation instant of slot `s`. -/
  proposal_time_succ_lt_confirmation_time : ∀ (E : Env V) (s : Slot), M.proposal_time E (s + 1) < M.confirmation_time E s
  /-- Every instant from the proposal instant of slot `s` to strictly before its confirmation
      instant lies in slot `s` or slot `s + 1`. -/
  slotOf_of_proposal_before_confirmation : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : M.proposal_time E s ≤ p) (hhi : p < M.confirmation_time E s), E.slotOf p = s ∨ E.slotOf p = s + 1
  /-- Every instant from the proposal instant of slot `s` to strictly before its view freeze lies in
      slot `s`. -/
  slotOf_of_proposal_before_freeze : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : M.proposal_time E s ≤ p) (hhi : p < M.view_freeze E s), E.slotOf p = s
  /-- If the proposal instant of slot `s` is at or before `t`, then `s` is at most the slot
      containing `t`. -/
  slot_le_slotOf_of_proposal_time_le : ∀ (E : Env V) {s : Slot} {t : Time} (h : M.proposal_time E s ≤ t), s ≤ E.slotOf t
  /-- The support cutoff of slot `s` is at or before its confirmation instant. -/
  Protocol_support_cutoff_le_confirmation_time : ∀ (E : Env V) (s : Slot), M.support_cutoff E s ≤ M.confirmation_time E s
  /-- The support cutoff of slot `s` is at or before the proposal instant of slot `s + 1`. -/
  support_cutoff_le_proposal_time_succ : ∀ (E : Env V) (s : Slot), M.support_cutoff E s ≤ M.proposal_time E (s + 1)
  /-- The support cutoff of slot `s` is strictly before the proposal instant of slot `s + 1`. -/
  support_cutoff_lt_proposal_time_succ : ∀ (E : Env V) (s : Slot), M.support_cutoff E s < M.proposal_time E (s + 1)
  /-- The view freeze of slot `s` plus one delay is strictly before its confirmation instant. -/
  view_freeze_add_delta_lt_confirmation_time : ∀ (E : Env V) (s : Slot), M.view_freeze E s + E.Δ < M.confirmation_time E s
  /-- The view freeze of slot `s` is strictly before its confirmation instant. -/
  view_freeze_lt_confirmation_time : ∀ (E : Env V) (s : Slot), M.view_freeze E s < M.confirmation_time E s
  /-- The view freeze of slot `s` is strictly before the Goldfish vote instant of slot `s + 1`. -/
  view_freeze_lt_vote_time_succ : ∀ (E : Env V) (s : Slot), M.view_freeze E s < M.vote_time E (s + 1)
  /-- The Goldfish vote instant of slot `s` is at or before its confirmation instant. -/
  Protocol_vote_time_le_confirmation_time : ∀ (E : Env V) (s : Slot), M.vote_time E s ≤ M.confirmation_time E s
  /-- The Goldfish vote instants grow with the slot. -/
  vote_time_mono_slots : ∀ (E : Env V) {a b : Slot} (hab : a ≤ b), M.vote_time E a ≤ M.vote_time E b
  /-- Two environments with the same delay `Δ` give every slot the same confirmation instant. -/
  confirmation_time_eq_of_delta_eq : ∀ {E E' : Env V} (h : E.Δ = E'.Δ) (s : Slot), M.confirmation_time E s = M.confirmation_time E' s
  /-- The confirmation instants grow with the slot. -/
  confirmation_time_mono : ∀ (S : Setup V) {s s' : Slot} (h : s ≤ s'), M.confirmation_time S.E s ≤ M.confirmation_time S.E s'
  /-- The confirmation instants grow with the slot. -/
  confirmation_time_mono_l78 : ∀ (S : Setup V) {s s' : Slot} (h : s ≤ s'), M.confirmation_time S.E s ≤ M.confirmation_time S.E s'
  /-- A signer with at most one vote in a vote set does not equivocate in it. -/
  equivocates_eq_false_of_card_le_one : ∀ {votes : Finset (GoldfishVote V)} {w : V} (h : (M.votes_by votes w).card ≤ 1), M.equivocates votes w = false
  /-- `w` equivocates in `votes` exactly when `votes` holds two different votes signed by `w`. -/
  equivocates_eq_true_iff : ∀ (votes : Finset (GoldfishVote V)) (w : V), M.equivocates votes w = true ↔
    ∃ u ∈ votes, ∃ u' ∈ votes, u ≠ u' ∧ u.val_index = w ∧ u'.val_index = w
  /-- If `votes ⊆ votes'` and `w` equivocates in `votes`, then `w` equivocates in `votes'`. -/
  equivocates_mono_of_subset : ∀ {votes votes' : Finset (GoldfishVote V)} (hsub : votes ⊆ votes') {w : V} (h : M.equivocates votes w = true), M.equivocates votes' w = true
  /-- Every instant is at or before some slot's confirmation instant. -/
  exists_confirmation_time_ge : ∀ (S : Setup V) (t : Time), ∃ s : Slot, t ≤ M.confirmation_time S.E s
  /-- `u` is in `M.votes_by votes v` exactly when `u` is in `votes` and its validator index is `v`. -/
  mem_votes_by_iff : ∀ (votes : Finset (GoldfishVote V)) (v : V) (u : GoldfishVote V), u ∈ M.votes_by votes v ↔ u ∈ votes ∧ u.val_index = v
  /-- `w` participates in `votes` exactly when `votes` holds a vote signed by `w`. -/
  participates_eq_true_iff : ∀ (votes : Finset (GoldfishVote V)) (w : V), M.participates votes w = true ↔ ∃ u ∈ votes, u.val_index = w
  /-- A signer that equivocates in a vote set participates in it. -/
  participates_of_equivocates : ∀ {votes : Finset (GoldfishVote V)} {w : V} (h : M.equivocates votes w = true), M.participates votes w = true
  /-- The proposal instant of slot `s` is a whole multiple of the delay `E.Δ`. -/
  proposal_time_emod_delta_inclX : ∀ (E : Env V) (s : Slot), M.proposal_time E s % E.Δ = 0
  /-- Two environments with the same delay `Δ` give every slot the same proposal instant. -/
  proposal_time_eq_of_delta_eq : ∀ {E E' : Env V} (h : E.Δ = E'.Δ) (s : Slot), M.proposal_time E s = M.proposal_time E' s
  /-- The proposal instant of every slot is nonnegative. -/
  Sts_proposal_time_nonneg : ∀ (S : Setup V) (s : Slot), (0 : Int) ≤ M.proposal_time S.E s
  /-- `M.proposal_wake_start S s` is at or before slot `s`'s proposal instant. -/
  proposal_wake_start_le_proposal_time : ∀ (S : Setup V) (s : Slot), M.proposal_wake_start S s ≤ M.proposal_time S.E s
  /-- `M.proposal_wake_start S s` is strictly before slot `s`'s proposal instant. -/
  proposal_wake_start_lt_proposal_time : ∀ (S : Setup V) (s : Slot), M.proposal_wake_start S s < M.proposal_time S.E s
  /-- A slot whose proposal instant is strictly after `0` is positive. -/
  slot_pos_of_proposal_time_pos_inclX : ∀ (E : Env V) {s : Slot} (h : 0 < M.proposal_time E s), 0 < s
  /-- The support cutoff of slot `s` is a whole multiple of the delay `S.E.Δ`. -/
  support_cutoff_emod_delta : ∀ (S : Setup V) (s : Slot), M.support_cutoff S.E s % S.E.Δ = 0
  /-- The support cutoff of slot `s` is at or before its confirmation instant. -/
  Sts_support_cutoff_le_confirmation_time : ∀ (E : Env V) (s : Slot), M.support_cutoff E s ≤ M.confirmation_time E s
  /-- The support cutoff of slot `s` is strictly before its view freeze. -/
  Sts_support_cutoff_lt_view_freeze : ∀ (E : Env V) (s : Slot), M.support_cutoff E s < M.view_freeze E s
  /-- The support cutoff of every slot is strictly after `0`. -/
  support_cutoff_pos : ∀ (S : Setup V) (s : Slot), 0 < M.support_cutoff S.E s
  /-- The Goldfish vote instant of slot `s` is strictly before the proposal instant of slot `s + 1`. -/
  voteTime_lt_nextProposal_l86d : ∀ (E : Env V) (s : Slot), M.vote_time E s < M.proposal_time E (s + 1)
  /-- If `tGAT + 8RΔ ≤ tE' ≤ slotStart s < tE` and `1 ≤ s`, the window
      `[slotStart (s − 1) + Δ − wVote S, slotStart (s − 1) + Δ]` lies inside `[tGAT, tE]`, and its
      end is at or before both `slotStart s + Δ` and the confirmation instant of slot `s − 1`. -/
  voteWindow_prev_inPhase : ∀ (S : Setup V) (tGAT tE tE' : Int) {s : Slot} (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hs1 : 1 ≤ s) (hs' : tE' ≤ slotStart S.E.Δ s) (hsE : slotStart S.E.Δ s < tE), tGAT ≤ slotStart S.E.Δ (s - 1) + S.E.Δ - wVote S ∧
    slotStart S.E.Δ (s - 1) + S.E.Δ ≤ tE ∧
    slotStart S.E.Δ (s - 1) + S.E.Δ ≤ slotStart S.E.Δ s + S.E.Δ ∧
    slotStart S.E.Δ (s - 1) + S.E.Δ ≤ M.confirmation_time S.E (s - 1)
  /-- The Goldfish vote instant of a slot plus one delay is at or before that slot's confirmation
      instant. -/
  vote_time_add_delta_le_confirmation_time : ∀ (S : Setup V) (s : Slot), M.vote_time S.E s + S.E.Δ ≤ M.confirmation_time S.E s
  /-- The Goldfish vote instant of slot `s` is a whole multiple of the delay `S.E.Δ`. -/
  vote_time_emod_delta : ∀ (S : Setup V) (s : Slot), M.vote_time S.E s % S.E.Δ = 0
  /-- The Goldfish vote instant of slot `s` is at or before its confirmation instant. -/
  Sts_vote_time_le_confirmation_time : ∀ (S : Setup V) (s : Slot), M.vote_time S.E s ≤ M.confirmation_time S.E s
  /-- The Goldfish vote instants grow with the slot. -/
  vote_time_mono : ∀ (E : Env V) {s s' : Slot} (h : s ≤ s'), M.vote_time E s ≤ M.vote_time E s'
  /-- The Goldfish vote instant of a positive slot is strictly after `0`. -/
  vote_time_pos : ∀ (S : Setup V) {s : Slot} (hs : 0 < s), 0 < M.vote_time S.E s
  /-- If the support cutoff of slot `k` is strictly before the Goldfish vote instant of slot `s`, it
      is strictly before the proposal instant of slot `s`. -/
  support_cutoff_lt_vote_time_imp_lt_proposal_time : ∀ (E : Env V) {k s : Slot} (h : M.support_cutoff E k < M.vote_time E s), M.support_cutoff E k < M.proposal_time E s
  /-- Every instant from the proposal instant of slot `s` to strictly before that of slot `s + 1`
      lies in slot `s`. -/
  slotOf_of_proposal_before_next_proposal : ∀ (E : Env V) (s : Slot) {p : Time} (hlo : M.proposal_time E s ≤ p) (hhi : p < M.proposal_time E (s + 1)), E.slotOf p = s
  /-- If `s + 2 ≤ s'`, the confirmation instant of slot `s` is strictly before the proposal instant
      of slot `s'`. -/
  confirmationTime_lt_proposalTime_of_two_le : ∀ (E : Env V) {s s' : Slot} (h : s + 2 ≤ s'), M.confirmation_time E s < M.proposal_time E s'
  /-- If the Goldfish vote `u` is for a slot from `st.s - 1` to `st.s`, is not already among `st`'s
      votes of its slot, and its validator does not equivocate in `st.pool u.slot`, then
      `M.on_goldfish_vote st u` appends `u` to its slot's votes, stamps it with `st.t`, and keeps
      everything else of these fields and the time. -/
  on_goldfish_vote_insert : ∀ (st : M.S) (u : GoldfishVote V) (h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot)) (h2 : ¬ M.equivocates (st.pool u.slot) u.val_index = true),
    (M.on_goldfish_vote st u).gf_votes =
      (fun k => if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k) ∧
    (M.on_goldfish_vote st u).timestamp_vote =
      (fun x => if x = u then some (st.t : Stamp) else st.timestamp_vote x) ∧
    (M.on_goldfish_vote st u).t = st.t
  /-- If `u` is in `gs.pool s` with a vote stamp strictly before the view freeze of slot `s`, and
      `u`'s head resolves in `gs`'s tree to a block `X` of a slot at most `u`'s, stamped strictly
      before that view freeze, then `u` is in every outcome of `M.voter_support_view E gs (s + 1)`. -/
  mem_voter_support_view_of_pool : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V} (hu : u ∈ gs.pool s) {τ : Stamp} (hτ : gs.timestamp_vote u = some τ) (hlt : τ < ((M.view_freeze E s : Int) : Stamp)) {X : Block V} (hX : Block.find? gs.T u.head = some X) (hXs : X.slot ≤ u.slot) {σ : Stamp} (hσ : gs.timestamp_block X = some σ) (hσlt : σ < ((M.view_freeze E s : Int) : Stamp))
    (W : Finset (GoldfishVote V)) (hW : M.voter_support_view E gs (s + 1) ⇢ W),
    u ∈ W
  /-- If the action instant of round `r` is strictly before the proposal instant of slot `s`, then
      `r` is at most the round of slot `s`. -/
  action_round_le_of_lt_proposal : ∀ (S : Setup V) {r : Round} {s : Slot} (hlt : M.a S.hc S.E.Δ r < M.proposal_time S.E s), r ≤ M.round_of S.hc s
  /-- One delay after the view freeze of slot `s` is at or before the proposal instant of slot
      `s + 1`. -/
  view_freeze_add_delta_le_proposal_time_succ : ∀ (E : Env V) (s : Slot),
    M.view_freeze E s + E.Δ ≤ M.proposal_time E (s + 1)
  /-- The Goldfish vote instant of slot `s` is at or before its view freeze. -/
  vote_time_le_view_freeze : ∀ (E : Env V) (s : Slot), M.vote_time E s ≤ M.view_freeze E s
  /-- The instants of slot `s` from its proposal instant: the vote instant is `Δ` after it, the
      support cutoff `2Δ`, the view freeze `3Δ`, the proposal instant of `s + 1` `4Δ`, the vote
      instant of `s + 1` `5Δ`, and the confirmation instant of `s` `6Δ`. -/
  slot_instants_l55 : ∀ (E : Env V) (s : Slot),
    M.vote_time E s = M.proposal_time E s + E.Δ ∧
      M.support_cutoff E s = M.proposal_time E s + 2 * E.Δ ∧
      M.view_freeze E s = M.proposal_time E s + 3 * E.Δ ∧
      M.proposal_time E (s + 1) = M.proposal_time E s + 4 * E.Δ ∧
      M.vote_time E (s + 1) = M.proposal_time E s + 5 * E.Δ ∧
      M.confirmation_time E s = M.proposal_time E s + 6 * E.Δ

/-- The facts about runs of the slot schedule of a model `M`; it has no field. -/
structure ScheduleRunFacts (M : Model V) : Prop where


end DecoupledConsensusModel.Sts.Record
