import Proofs.Instance.Objects
import Spec
import Model.Vocabulary

/-!
# Equalities for the validator-client routines

For each member of the validator-client family of the record, the `DecoupledConsensusModel` routine
filling it, applied to the `toProof` images of the spec's data, equals the image of the spec's
routine. The image of a signing history `sh` as a signing record is `sh.toProof.legacy`.
-/

set_option autoImplicit false

namespace SpecRecord

open Spec

variable {V : Type}

private theorem getElem_fun {α β : Type} (f : α → β) (a : α) : f[a] = f a := rfl

private theorem value_some {α : Type} (a : α) (h : some a ≠ none) : (some a).value h = a := rfl

private theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- The record's member `own_lock`: `DecoupledConsensusModel.Protocol.own_lock` of
    `sh.toProof.legacy` at `h_c` and the image of `fp` is the image of the spec's
    `Protocol.own_lock sh h_c fp`. -/
theorem toProof_own_lock (sh : SigningHistory) (h_c : Height) (fp : Option FinalityPair) :
    DecoupledConsensusModel.Protocol.own_lock sh.toProof.legacy h_c
        (fp.map FinalityPair.toProof) =
      (Protocol.own_lock sh h_c fp).map BlockId.toProof := by
  cases fp with
  | none => rfl
  | some p =>
    simp only [DecoupledConsensusModel.Protocol.own_lock, Protocol.own_lock, Id.run,
      Option.map_some, FinalityPair.toProof, SigningHistory.toProof_legacy_lock, getElem_fun,
      value_some, id_pure, ne_eq, reduceCtorEq, not_false_eq_true, dite_true]
    split_ifs <;> rfl

/-- The record's member `finality_pair`: `DecoupledConsensusModel.Protocol.finality_pair` of
    `sh.toProof.legacy` at `h_j`, the image of `J` and `h_F` is the image of the spec's
    `Protocol.finality_pair sh h_j J h_F`. -/
theorem toProof_finality_pair (sh : SigningHistory) (h_j : Height) (J : BlockId) (h_F : Height) :
    DecoupledConsensusModel.Protocol.finality_pair sh.toProof.legacy h_j J.toProof h_F =
      (Protocol.finality_pair sh h_j J h_F).map FinalityPair.toProof := by
  simp only [DecoupledConsensusModel.Protocol.finality_pair, Protocol.finality_pair, Id.run,
    SigningHistory.toProof_legacy_target, SigningHistory.toProof_legacy_timeout,
    SigningHistory.toProof_legacy_lock, getElem_fun, id_pure]
  by_cases hF : h_j ≤ h_F
  · rw [if_neg (Nat.not_lt.mpr hF), if_pos hF]
    rfl
  · rw [if_pos (Nat.lt_of_not_le hF), if_neg hF]
    split_ifs <;>
      first
        | (simp_all [FinalityPair.toProof]; done)
        | (simp_all [FinalityPair.toProof]; tauto)

/-- The record's member `height_pair`: `DecoupledConsensusModel.Protocol.height_pair` of
    `sh.toProof.legacy` at the images of `fields` and `fp` is the image of the spec's
    `Protocol.height_pair sh fields fp`. -/
theorem toProof_height_pair (sh : SigningHistory) (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) :
    DecoupledConsensusModel.Protocol.height_pair sh.toProof.legacy
        (fields.map (fun f => (f.1, f.2.1.toProof, f.2.2))) (fp.map FinalityPair.toProof) =
      (Protocol.height_pair sh fields fp).toProof := by
  rcases fields with _ | ⟨h_c, T_c, ν⟩
  · rfl
  · simp only [DecoupledConsensusModel.Protocol.height_pair, Protocol.height_pair, Id.run,
      Option.map_some, toProof_own_lock, getElem_fun, SigningHistory.toProof_legacy_timeout,
      SigningHistory.toProof_legacy_target, value_some, id_pure, ne_eq, reduceCtorEq,
      not_false_eq_true, dite_true]
    generalize Protocol.own_lock sh h_c fp = lk
    generalize sh.target h_c = t
    cases sh.timeout h_c
    · cases lk with
      | some b =>
        by_cases hb : b = T_c
        · simp [hb, HeightPair.toProof]
        · simp [hb, HeightPair.toProof]
      | none =>
        cases t with
        | some b =>
          by_cases hb : b = T_c
          · simp [hb, HeightPair.toProof]
          · simp [hb, HeightPair.toProof]
        | none => cases ν <;> rfl
    · rfl

/-! ## The attestation and the signing history -/

/-- The record's member `record_attestation`: `DecoupledConsensusModel.Protocol.record_attestation`
    of `sh.toProof.legacy` and the image of `a` is
    `(Protocol.record_attestation sh a).toProof.legacy`. -/
theorem toProof_record_attestation (sh : SigningHistory) (a : Attestation V) :
    DecoupledConsensusModel.Protocol.record_attestation sh.toProof.legacy a.toProof =
      (Protocol.record_attestation sh a).toProof.legacy := by
  obtain ⟨v, r, c, hp, fp⟩ := a
  cases fp <;> rcases hp with _ | ⟨h, entry, _ | _⟩ <;>
    simp only [DecoupledConsensusModel.Protocol.record_attestation, Protocol.record_attestation,
      Id.run, Attestation.toProof, Option.map_some, Option.map_none, HeightPair.toProof,
      FinalityPair.toProof, value_some, id_pure, ne_eq, reduceCtorEq, not_false_eq_true,
      dite_true, not_true_eq_false, dite_false, HeightPair.pairHeight?, HeightPair.target?,
      getElem_fun]
  all_goals
    try simp only [DecoupledConsensusModel.Protocol.Record.with_lock,
      SigningHistory.toProof_legacy_target, Option.map_eq_none_iff]
    try split_ifs
    all_goals
      simp only [SigningHistory.toProof, DecoupledConsensusModel.Protocol.Record.with_timeout,
        DecoupledConsensusModel.Protocol.Record.with_target,
        DecoupledConsensusModel.Protocol.Record.mk.injEq]
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals
      first
        | trivial
        | (funext k
           try simp only [Function.update_apply]
           all_goals (try split_ifs)
           all_goals rfl)

/-- The record's member `create_attestation`: `DecoupledConsensusModel.Protocol.create_attestation`
    of `sh.toProof.legacy`, `v`, `r` and the images of the data is the spec's
    `Protocol.create_attestation` at the same data, its signing history mapped to a signing record
    and its attestation mapped. -/
theorem toProof_create_attestation (sh : SigningHistory) (v : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height)
    (J : BlockId) (h_F : Height) :
    DecoupledConsensusModel.Protocol.create_attestation sh.toProof.legacy v r
        (confirmed.map BlockId.toProof) (fields.map (fun f => (f.1, f.2.1.toProof, f.2.2))) h_j
        J.toProof h_F =
      Prod.map (fun x : SigningHistory => x.toProof.legacy) Attestation.toProof
        (Protocol.create_attestation sh v r confirmed fields h_j J h_F) := by
  simp only [DecoupledConsensusModel.Protocol.create_attestation, toProof_finality_pair,
    toProof_height_pair]
  exact Prod.ext (toProof_record_attestation sh ⟨v, r, confirmed,
    Protocol.height_pair sh fields (Protocol.finality_pair sh h_j J h_F),
    Protocol.finality_pair sh h_j J h_F⟩) rfl

end SpecRecord
