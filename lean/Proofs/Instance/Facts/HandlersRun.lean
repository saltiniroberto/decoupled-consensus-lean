import Proofs.Instance.Facts.Handlers
import Proofs.Instance.RunInvariant

/-!
# Two run facts at `Model.spec`

Proofs of the fields `finalizedViable_stateBeforeTime` and `sgRowRounds_stateBeforeTime` of
`HandlersRunFacts` at `Model.spec`, and of `ConfirmedInTree` along the steps of a store.
-/

namespace SpecRecord.HandlersRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The attestations of each round are of that round -/

/-- The field `sgRowRounds_stateBeforeTime` of `HandlersRunFacts` at `Model.spec`: in every
    world the events of `rho` with time less than `t` can reach from the initial world, every named
    attestation of round `r` in `v`'s store is of round `r`. -/
theorem spec_sgRowRounds_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time)
    (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u),
      ∀ (r : Round), ∀ row ∈ (w₁ v).st.sg_rows r, row.round = r := by
  intro S rho t v w₁ hw₁ r row hrow
  have hI := rows_fold_ok S _ w₁ hw₁ v
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt row
  exact hI r a' ((mem_sg_rows_iff (w₁ v).val.st r a').1 hrow)

/-! ## The finalized block is viable -/

/-- `ViableInv st`: `FinalizedViable` of the image of `st`: the finalized block is in the tree, and
    some tree block descending from it has a chain state of height at least `h_max - 1`. -/
def ViableInv (st : Spec.Store V) : Prop :=
  DecoupledConsensusModel.Proofs.FinalizedViable st.toProof

/-- Every step into a store with distinct roots keeps `ViableInv`, given `StoreOk` and
    `RunStoreInv`. -/
theorem viableInv_step (S : Setup V) (τ : Time) (a b : Spec.Store V)
    (hs : StoreSteps.StoreStep (Setup.toSpec S).C (Setup.toSpec S).P τ a b)
    (hd : DistinctRoots b.T) (h : StoreOk a ∧ SubtypeEqualities.RunStoreInv a ∧ ViableInv a) :
    StoreOk b ∧ SubtypeEqualities.RunStoreInv b ∧ ViableInv b := by
  obtain ⟨hb1, hb2⟩ := base_step hs hd ⟨h.1, h.2.1⟩
  refine ⟨hb1, hb2, ?_⟩
  have hj := h.2.2
  cases hs with
  | grades g => exact hj
  | clock => exact DecoupledConsensusModel.Proofs.finalizedViable_of_eq (st := a.toProof) rfl rfl rfl rfl hj
  | confirm x y z => exact DecoupledConsensusModel.Proofs.finalizedViable_of_eq (st := a.toProof) rfl rfl rfl rfl hj
  | vote u =>
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes (Setup.toSpec S).P a u
    rw [e]
    exact DecoupledConsensusModel.Proofs.finalizedViable_of_eq (st := a.toProof) rfl rfl rfl rfl hj
  | attest row =>
    have h1 := (priv% Proofs.Vocabulary.Execution.FinalizedViable
      DecoupledConsensusModel.Proofs.NamedFinalizedViable.viable_row) S.hc a.toProofNamed
      row.toProofNamed hj
    rw [toProof_admit_row S.E S.hc S.cfg] at h1
    exact h1
  | block B =>
    rcases SubtypeEqualities.on_block_cases_of_ok _ _ hd with e | hroot
    · rw [e]
      exact hj
    · have h1 := (priv% Proofs.Vocabulary.Execution.FinalizedViable
        DecoupledConsensusModel.Proofs.NamedFinalizedViable.viable_block_with) S a.toProofNamed
        B.toProofNamed hj
      rw [← image_on_block_step S h.1 h.2.1 B hroot] at h1
      exact h1

omit [Fintype V] [Inhabited V] in
/-- The initial store has `ViableInv`. -/
theorem viableInv_init : ViableInv (Spec.Store.init : Spec.Store V) := by
  unfold ViableInv
  rw [DecoupledConsensusModel.Proofs.finalizedViable_iff]
  refine ⟨Finset.mem_image_of_mem _ (by simp [Spec.Store.init]),
    (Spec.Store.init : Spec.Store V).F.toProof,
    Finset.mem_image_of_mem _ (by simp [Spec.Store.init]),
    DecoupledConsensusModel.Block.preceq_self _, ?_⟩
  show (1 : Nat) - 1 ≤ _
  exact Nat.zero_le _

/-- The field `finalizedViable_stateBeforeTime` of `HandlersRunFacts` at `Model.spec`: in every
    world the events of `rho` with time less than `t` can reach from the initial world, the
    finalized block of `v`'s store is in its tree, and some tree block `W` descending from it has a
    chain-state height at least `h_max - 1`. -/
theorem spec_finalizedViable_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u),
      (w₁ v).st.core.F ∈ (w₁ v).st.core.T ∧ ∃ W ∈ (w₁ v).st.core.T,
        Block.Preceq (w₁ v).st.core.F W ∧ (w₁ v).st.core.h_max - 1 ≤ ((w₁ v).st.core.σ W).h := by
  intro S rho t v w₁ hw₁
  have h := (DecoupledConsensusModel.Proofs.finalizedViable_iff _).mp
    (inv_fold S ViableInv (viableInv_step S) viableInv_init _ w₁ hw₁ v)
  obtain ⟨hF, W, hW, hFW, hh⟩ := h
  refine ⟨hF, W, hW, ?_, hh⟩
  unfold DecoupledConsensusModel.Block.Preceq
  exact hFW

/-! ## The confirmation records stay in the tree -/

omit [Fintype V] [Inhabited V] in
/-- A store `st'` with the three confirmation records of `st` and a tree holding every block of
    `st.T` has `ConfirmedInTree` when `st` has it. -/
private theorem sameConfirmed_with {st st' : Spec.Store V}
    (h1 : st'.live_confirmed = st.live_confirmed) (h2 : st'.latest_confirmed = st.latest_confirmed)
    (h3 : st'.latest_stable = st.latest_stable) (hT : ∀ X ∈ st.T, X ∈ st'.T)
    (h : ConfirmedInTree st) : ConfirmedInTree st' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact hT _ h.1
  · rw [h2]; exact hT _ h.2.1
  · rw [h3]; exact hT _ h.2.2

omit [Inhabited V] in
/-- `Protocol.on_block` keeps `live_confirmed`, `latest_confirmed` and `latest_stable`. -/
theorem on_block_confirmed (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).live_confirmed = st.live_confirmed ∧
      (Spec.Protocol.on_block C P st B).latest_confirmed = st.latest_confirmed ∧
      (Spec.Protocol.on_block C P st B).latest_stable = st.latest_stable := by
  rcases StoreSteps.on_block_shape C P st B with e | ⟨-, σ', e⟩
  · rw [e]; exact ⟨rfl, rfl, rfl⟩
  · rw [e]
    generalize hX : List.foldl (Spec.Protocol.on_goldfish_vote_checked P) _ _ = X
    obtain ⟨x0, y0, e0⟩ := StoreSteps.foldl_checked_writes P B.gf_votes
      { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }
    rw [e0] at hX
    subst hX
    obtain ⟨a, b, c, d, e1⟩ := StoreSteps.update_finality_writes
      { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)),
                gf_votes := x0, timestamp_vote := y0 } B
    rw [e1]
    obtain ⟨x, y, e2⟩ := StoreSteps.admit_attestations_writes C B.attestations _
    rw [e2]
    exact ⟨rfl, rfl, rfl⟩

/-- Every step from a store with `StoreOk`, `RunStoreInv` and `ConfirmedInTree` keeps
    `ConfirmedInTree`. -/
theorem confirmedInTree_step {C : Spec.Config} {P : Spec.Provisional V}
    {τ : Time} {a b : Spec.Store V} (hs : StoreSteps.StoreStep C P τ a b)
    (hok : StoreOk a) (hinv : SubtypeEqualities.RunStoreInv a) (h : ConfirmedInTree a) :
    ConfirmedInTree b := by
  have hT : ∀ X ∈ a.T, X ∈ b.T := fun X hX => (keepsBlocks_step hs X hX).1
  cases hs with
  | grades g => exact h
  | clock => exact h
  | confirm x y z hm =>
    obtain ⟨h1, h2, h3⟩ := hm hok.2.2.2 hinv.1 h.2.1 h.2.2
    exact ⟨h1, h2, h3⟩
  | vote u =>
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes P a u
    rw [e] at hT ⊢
    exact sameConfirmed_with rfl rfl rfl hT h
  | attest row =>
    obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C a row
    rw [e] at hT ⊢
    exact sameConfirmed_with rfl rfl rfl hT h
  | block B =>
    obtain ⟨e1, e2, e3⟩ := on_block_confirmed C P a B
    exact sameConfirmed_with e1 e2 e3 hT h

omit [Fintype V] [Inhabited V] in
/-- The initial store has `ConfirmedInTree`. -/
theorem confirmedInTree_init :
    ConfirmedInTree (Spec.Store.init : Spec.Store V) :=
  ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩

end SpecRecord.HandlersRunFacts
