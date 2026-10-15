module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
public import Proofs.Vocabulary.Protocol.ChainState.TargetedTimeoutBinding
public import Proofs.Vocabulary.Protocol.ChainState.NjGap

@[expose] public section

/-!
# Facts about `Protocol.fold_rows`

The row fold of a chain-state transition, which sets the slot to the geometry's slot, folds
`process_attestation_with` over the rows and sets `L` to the geometry, at the timeout binding
`TimeoutBinding.targeted`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.TimeoutBinding.view

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

section ChainStateBodies

attribute [local semireducible] Protocol.fold_rows Protocol.process_attestation_with
  Protocol.process_attestation

omit [Fintype V] in
/-- The targeted row fold keeps the finalized block. -/
theorem fold_rows_F (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).F = st.F :=
  (Proofs.NamedDerivationGeometry.fold_context_fields (Protocol.TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.2.2.1

omit [Fintype V] in
/-- The targeted row fold keeps the finalized height. -/
theorem fold_rows_h_F (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).h_F = st.h_F :=
  (Proofs.NamedDerivationGeometry.fold_context_fields (Protocol.TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
/-- The targeted row fold keeps the justified block. -/
theorem fold_rows_J (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).J = st.J :=
  (Proofs.NamedDerivationGeometry.fold_context_fields (Protocol.TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
/-- The targeted row fold keeps the justified height. -/
theorem fold_rows_h_j (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j :=
  (Proofs.NamedDerivationGeometry.fold_context_fields (Protocol.TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.2.1

omit [Fintype V] in
/-- After the targeted row fold, the chain state's slot is the geometry's slot. -/
theorem fold_rows_s_l85 (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).s =
      geometry.slot := by
  have key : ∀ (rs : List (NamedAttestation V)) (σ : Protocol.ChainState V),
      (rs.foldl (Protocol.process_attestation_with (Protocol.TimeoutBinding.targeted V)) σ).s =
        σ.s := by
    intro rs
    induction rs with
    | nil => intro σ; rfl
    | cons r rs ih =>
      intro σ
      rw [List.foldl_cons, ih]
      unfold Protocol.process_attestation_with Protocol.process_attestation
      split_ifs <;> rfl
  unfold Protocol.fold_rows
  exact key rows { st with s := geometry.slot }

omit [Fintype V] in
/-- The targeted row fold keeps the height, the entry and the `nj` bit. -/
theorem fold_rows_fields_l85 (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).h = st.h ∧
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).T_h = st.T_h ∧
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).nj = st.nj := by
  have hf := Proofs.NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) rows { st with s := geometry.slot }
  refine ⟨hf.2.1, hf.2.2.1, ?_⟩
  have key : ∀ (σ : Protocol.ChainState V) (rs : List (NamedAttestation V)),
      (List.foldl (Protocol.process_attestation_with (Protocol.TimeoutBinding.targeted V))
        σ rs).nj = σ.nj := by
    intro σ rs
    induction rs generalizing σ with
    | nil => rfl
    | cons r rs ih2 =>
      rw [List.foldl_cons, ih2]
      exact Proofs.NjGap.process_attestation_nj σ _
  unfold Protocol.fold_rows
  exact key _ rows

omit [Fintype V] in
/-- The targeted row fold only adds to the progress set. -/
theorem fold_rows_progress_subset (st : Protocol.ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    st.progress ⊆
      (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).progress := by
  have key : ∀ (rs : List (NamedAttestation V)) (σ : Protocol.ChainState V),
      σ.progress ⊆
        (rs.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V)) σ).progress := by
    intro rs
    induction rs with
    | nil => intro σ; exact Finset.Subset.refl _
    | cons row rs ih =>
      intro σ
      rw [List.foldl_cons]
      apply Finset.Subset.trans _ (ih _)
      intro signer hsigner
      rw [(Proofs.TargetedTimeoutBinding.process_height_fields σ row).1]
      split_ifs
      · exact Finset.mem_insert_of_mem hsigner
      · exact hsigner
  unfold Protocol.fold_rows
  exact key rows { st with s := geometry.slot }

omit [Fintype V] in
/-- If the row `a` is among `rows` and its height pair matches `st`'s height and the root of `st`'s
    entry, then `a`'s signer is in the progress set after the targeted row fold of `rows`. -/
theorem fold_rows_mem_progress_of_matching (st : Protocol.ChainState V) (geometry : Block V)
    {rows : List (NamedAttestation V)} {a : NamedAttestation V} (ha : a ∈ rows)
    (hmatch : a.height_pair.matchesEntry st.h st.T_h.root = true) :
    a.val_index ∈
      (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) st geometry rows).progress := by
  have hsub : ∀ (rs : List (NamedAttestation V)) (σ : Protocol.ChainState V),
      σ.progress ⊆
        (rs.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V)) σ).progress := by
    intro rs
    induction rs with
    | nil => intro σ; exact Finset.Subset.refl _
    | cons row rs ih =>
      intro σ
      rw [List.foldl_cons]
      apply Finset.Subset.trans _ (ih _)
      intro signer hsigner
      rw [(Proofs.TargetedTimeoutBinding.process_height_fields σ row).1]
      split_ifs
      · exact Finset.mem_insert_of_mem hsigner
      · exact hsigner
  have key : ∀ (rs : List (NamedAttestation V)) (σ : Protocol.ChainState V),
      a ∈ rs → a.height_pair.matchesEntry σ.h σ.T_h.root = true →
      a.val_index ∈
        (rs.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V)) σ).progress := by
    intro rs
    induction rs with
    | nil => intro σ h _; simp at h
    | cons row rs ih =>
      intro σ h hm
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | htail
      · apply hsub
        rw [(Proofs.TargetedTimeoutBinding.process_height_fields σ a).1, if_pos hm]
        exact Finset.mem_insert_self _ _
      · apply ih _ htail
        have hfields := Proofs.TimeoutBindingDefaults.process_context_fields
          (Protocol.TimeoutBinding.targeted V) σ row
        rw [hfields.2.1, hfields.2.2.1]
        exact hm
  unfold Protocol.fold_rows
  exact key rows { st with s := geometry.slot } ha hmatch

end ChainStateBodies

end DecoupledConsensusModel.Sts
