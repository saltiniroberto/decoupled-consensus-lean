import Proofs.Vocabulary.Protocol.Grades.Main
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_voters_count
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_score

/-!
# Facts about `Protocol.update_confirmation_with`

Lemmas that unfold the confirmation update: its write of `latest_confirmed` and the fields it keeps.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.beforeCutoff

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The `latest_confirmed` that `update_confirmation_with` writes is `floor_on_stable` of the
    `latest_stable` it writes, a candidate `cand`, and the store's `latest_confirmed`; and `cand` is
    the store's `latest_confirmed`, or `advance_confirmed` of it with the confirmation walk's result
    `W` when the store passes the slot's eligibility test for `W`, or `advance_confirmed` of it with
    a block `G` the contract's `optional select` candidate answers at the store and slot. -/
theorem update_confirmation_with_latest_confirmed_cases
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) :
    ∃ cand : Block V,
      (Protocol.update_confirmation_with contract E hc st s).latest_confirmed
        = Protocol.floor_on_stable
            (Protocol.update_confirmation_with contract E hc st s).latest_stable cand
            st.latest_confirmed ∧
      (cand = st.latest_confirmed ∨
        (Protocol.confEligible E st s (Protocol.confWalkWith contract E hc st s) = true ∧
          cand = Protocol.advance_confirmed st.latest_confirmed
            (Protocol.confWalkWith contract E hc st s)) ∨
        ∃ (select : Env V → Protocol.HealConfig → Protocol.HealingStore V → Slot →
            Option (Block V)) (G : Block V),
          contract.confirmationSG = Protocol.ConfirmationSGCandidate.optional select ∧
          select E hc st.toHealing s = some G ∧
          cand = Protocol.advance_confirmed st.latest_confirmed G) := by
  obtain ⟨select, hmode⟩ : ∃ select, contract.confirmationSG =
      Protocol.ConfirmationSGCandidate.optional select := by
    cases h : contract.confirmationSG with
    | optional select => exact ⟨select, rfl⟩
  refine ⟨if Protocol.confEligible E st s (Protocol.confWalkWith contract E hc st s) then
      Protocol.advance_confirmed st.latest_confirmed (Protocol.confWalkWith contract E hc st s)
    else match select E hc st.toHealing s with
      | some candidate => Protocol.advance_confirmed st.latest_confirmed candidate
      | none => st.latest_confirmed, ?_, ?_⟩
  · show Protocol.floor_on_stable _ (match contract.confirmationSG with
        | .optional select =>
          if Protocol.confEligible E st s (Protocol.confWalkWith contract E hc st s) then
            Protocol.advance_confirmed st.latest_confirmed
              (Protocol.confWalkWith contract E hc st s)
          else match select E hc st.toHealing s with
            | some candidate => Protocol.advance_confirmed st.latest_confirmed candidate
            | none => st.latest_confirmed) st.latest_confirmed = _
    rw [hmode]
    rfl
  · split_ifs with hel
    · exact Or.inr (Or.inl ⟨hel, rfl⟩)
    · cases hsel : select E hc st.toHealing s with
      | none => exact Or.inl rfl
      | some G => exact Or.inr (Or.inr ⟨select, G, hmode, hsel, rfl⟩)

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store `update_confirmation_with` returns for the slot `s` has the clock of the store `st` it
    was given. -/
theorem update_confirmation_with_t (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).t = st.t := rfl


/-- The confirmation update leaves the Goldfish vote buckets unchanged. -/
theorem update_confirmation_with_gf_votes (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).gf_votes = st.gf_votes := rfl

/-- The confirmation update leaves the Goldfish vote stamps unchanged. -/
theorem update_confirmation_with_timestamp_vote (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).timestamp_vote = st.timestamp_vote :=
  rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the contract's stable root for the store's round is `G`, the `latest_stable` that
    `update_confirmation_with` writes is `advance_confirmed` of the store's `latest_stable` with
    `G`. -/
theorem update_confirmation_with_latest_stable_of_root
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) {G : Block V}
    (hG : contract.stableRoot E hc st.toHealing (hc.round_of st.s) = some G) :
    (Protocol.update_confirmation_with contract E hc st s).latest_stable
      = Protocol.advance_confirmed st.latest_stable G := by
  show (match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
    | some G => Protocol.advance_confirmed st.latest_stable G
    | none => st.latest_stable) = _
  rw [hG]

/-- If the contract's stable root for the store's round is `G` and `G` is an ancestor of the store's
    `latest_stable`, then `update_confirmation_with` leaves `latest_stable` unchanged and writes a
    `latest_confirmed` that is a descendant of it. -/
theorem update_confirmation_with_keeps_stable_of_root_preceq
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) {G : Block V}
    (hG : contract.stableRoot E hc st.toHealing (hc.round_of st.s) = some G)
    (hGo : Block.Preceq G st.latest_stable) :
    (Protocol.update_confirmation_with contract E hc st s).latest_stable = st.latest_stable ∧
      Block.Preceq st.latest_stable
        (Protocol.update_confirmation_with contract E hc st s).latest_confirmed := by
  have hadv : Protocol.advance_confirmed st.latest_stable G = st.latest_stable :=
    advance_confirmed_of_preceq hGo
  have hstab : (Protocol.update_confirmation_with contract E hc st s).latest_stable
      = st.latest_stable := by
    show (match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
      | some G => Protocol.advance_confirmed st.latest_stable G
      | none => st.latest_stable) = _
    rw [hG]
    exact hadv
  refine ⟨hstab, ?_⟩
  show Block.Preceq st.latest_stable (Protocol.floor_on_stable
    (match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
      | some G => Protocol.advance_confirmed st.latest_stable G
      | none => st.latest_stable) _ st.latest_confirmed)
  rw [hG]
  dsimp only
  rw [hadv]
  exact floor_on_stable_stable_preceq _ _ _

/-- The confirmation update leaves the tree `T` unchanged. -/
theorem update_confirmation_with_T (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).T = st.T := rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The confirmation update leaves the SG-vote lists unchanged. -/
theorem update_confirmation_with_sg_votes_eq (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).sg_votes = st.sg_votes := rfl

end DecoupledConsensusModel.Sts
