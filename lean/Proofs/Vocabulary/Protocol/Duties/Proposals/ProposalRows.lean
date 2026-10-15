module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.Store
public import Proofs.Vocabulary.Protocol.Handlers.NamedStore
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Proposal rows

Facts about the rows a named proposal carries: the processed and carried rows, on-chain exclusion,
and the per-signer cap.
-/
namespace DecoupledConsensusModel.Proofs.NamedProposalRows
open Protocol.NamedProposalRows
variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- Under `NamedStore.PoolView`, erasing the processed named rows gives the store's processed
    attestations, in order. -/
theorem processed_rows_erasure (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (hPool : NamedStore.PoolView st) :
    (processedRows hc st).map NamedAttestation.erase = st.core.processed_attestations hc := by
  have key : ∀ rs : List Round,
      (rs.flatMap st.sg_rows).map NamedAttestation.erase = rs.flatMap st.core.sg_votes := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rs ih => simp only [List.flatMap_cons, List.map_append, hPool r, ih]
  exact key _


theorem selected_source_exact (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) :
    select .poolAndCarried hc st = poolRows hc st ++ carriedRows hc st := rfl


theorem ordered_bodies_mem {st : Protocol.NamedStore V} {B : NamedBlock V}
    (hB : B ∈ orderedBodies st) : B ∈ st.bodies := by
  obtain ⟨root, _, hfind⟩ := List.mem_filterMap.mp hB
  exact Proofs.Engine.pickUnique?_mem hfind


/-- A row is carried exactly when it is an attestation of an eligible ordered body and its round is
    in the store's window. -/
theorem mem_carried_rows (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    row ∈ carriedRows hc st ↔ ∃ B ∈ orderedBodies st,
      eligibleBody hc st B = true ∧ row ∈ B.attestations ∧
        Protocol.ProposalRows.inWindow hc st.core row.round = true := by
  simp only [carriedRows, List.mem_flatMap]
  constructor
  · rintro ⟨B, hB, hrow⟩
    by_cases he : eligibleBody hc st B = true
    · exact ⟨B, hB, he, by simpa [he] using hrow⟩
    · simp [he] at hrow
  · rintro ⟨B, hB, he, hrow⟩
    exact ⟨B, hB, by simpa [he] using hrow⟩


/-- A row survives on-chain exclusion exactly when it is in `rows` and not among the rows of
    `head`'s chain. -/
theorem mem_exclude_on_chain (head : NamedBlock V) (rows : List (NamedAttestation V))
    (row : NamedAttestation V) :
    row ∈ excludeOnChain head rows ↔ row ∈ rows ∧ row ∉ chainRows head := by
  simp [excludeOnChain]

private theorem mem_cap_foldl (rows acc : List (NamedAttestation V))
    (row : NamedAttestation V)
    (h : row ∈ rows.foldl (fun kept next =>
      if next ∈ kept ||
          decide (2 ≤ (kept.filter (fun a =>
            decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
      then kept else kept ++ [next]) acc) : row ∈ acc ∨ row ∈ rows := by
  induction rows generalizing acc with
  | nil => exact Or.inl h
  | cons next rest ih =>
      simp only [List.foldl_cons] at h
      rcases ih _ h with hacc | hrest
      · split at hacc
        · exact Or.inl hacc
        · rcases List.mem_append.mp hacc with hacc | hnext
          · exact Or.inl hacc
          · refine Or.inr ?_
            simp only [List.mem_cons]
            exact Or.inl (by simpa using hnext)
      · exact Or.inr (by simp [hrest])

/-- Every row the per-signer cap keeps is in `rows`. -/
theorem mem_capPerSigner (rows : List (NamedAttestation V))
    (row : NamedAttestation V) (h : row ∈ capPerSigner rows) : row ∈ rows := by
  exact (mem_cap_foldl rows [] row h).resolve_left (by simp)

private theorem mem_cap_foldl_of_unique
    (all remaining acc : List (NamedAttestation V)) (row : NamedAttestation V)
    (hacc : ∀ b ∈ acc, b ∈ all)
    (hremaining : ∀ b ∈ remaining, b ∈ all)
    (hunique : ∀ b ∈ all,
      b.val_index = row.val_index → b.round = row.round → b = row)
    (ha : row ∈ acc ∨ row ∈ remaining) :
    row ∈ remaining.foldl (fun kept next =>
      if next ∈ kept ||
          decide (2 ≤ (kept.filter (fun a =>
            decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
      then kept else kept ++ [next]) acc := by
  induction remaining generalizing acc with
  | nil =>
      rcases ha with h | h
      · exact h
      · simp at h
  | cons next tail ih =>
      let acc' : List (NamedAttestation V) :=
        if next ∈ acc ||
            decide (2 ≤ (acc.filter (fun a =>
              decide (a.val_index = next.val_index ∧ a.round = next.round))).length)
        then acc else acc ++ [next]
      have hnext : next ∈ all := hremaining next (by simp)
      have hacc' : ∀ b ∈ acc', b ∈ all := by
        intro b hb
        dsimp [acc'] at hb
        split at hb
        · exact hacc b hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact hacc b hb
          · have hbeq : b = next := by simpa using hb
            rw [hbeq]
            exact hnext
      have htail : ∀ b ∈ tail, b ∈ all := by
        intro b hb
        exact hremaining b (by simp [hb])
      have ha' : row ∈ acc' ∨ row ∈ tail := by
        rcases ha with h | h
        · left
          dsimp [acc']
          split
          · exact h
          · exact List.mem_append.mpr (Or.inl h)
        · rcases List.mem_cons.mp h with h | h
          · subst next
            left
            by_cases hm : row ∈ acc
            · dsimp [acc']
              split
              · exact hm
              · exact List.mem_append.mpr (Or.inl hm)
            · have hf : (acc.filter (fun b =>
                  decide (b.val_index = row.val_index ∧ b.round = row.round))) = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro b hb hkey
                have hkey' : b.val_index = row.val_index ∧ b.round = row.round :=
                  of_decide_eq_true hkey
                exact hm ((hunique b (hacc b hb) hkey'.1 hkey'.2) ▸ hb)
              have hguard : (decide (row ∈ acc) ||
                  decide (2 ≤ (acc.filter (fun b =>
                    decide (b.val_index = row.val_index ∧ b.round = row.round))).length)) =
                  false := by
                have hlim : ¬ 2 ≤ (acc.filter (fun b =>
                    decide (b.val_index = row.val_index ∧ b.round = row.round))).length := by
                  simp only [hf, List.length_nil]
                  decide
                exact Bool.or_eq_false_iff.mpr
                  ⟨decide_eq_false hm, decide_eq_false hlim⟩
              simp only [acc', hguard]
              simp
          · exact Or.inr h
      simpa only [List.foldl_cons] using ih acc' hacc' htail ha'

/-- A row of `rows` that is the only one of its signer and round survives the per-signer cap. -/
theorem mem_capPerSigner_of_unique (rows : List (NamedAttestation V))
    (row : NamedAttestation V) (hrow : row ∈ rows)
    (hunique : ∀ b ∈ rows,
      b.val_index = row.val_index → b.round = row.round → b = row) :
    row ∈ capPerSigner rows := by
  exact mem_cap_foldl_of_unique rows rows [] row (by simp)
    (fun _ h => h) hunique (Or.inr hrow)

/-- A row of `proposalRows parent rows` is in `rows`. -/
theorem mem_proposalRows (parent : NamedBlock V)
    (rows : List (NamedAttestation V)) (row : NamedAttestation V)
    (h : row ∈ proposalRows parent rows) :
    row ∈ rows ∧ row ∉ chainRows parent := by
  exact (mem_exclude_on_chain parent rows row).mp (mem_capPerSigner _ _ h)

/-- A row of `rows` that is the only one of its signer and round, and is not among the rows of
    `parent`'s chain, is in `proposalRows parent rows`. -/
theorem mem_proposalRows_of_unique (parent : NamedBlock V)
    (rows : List (NamedAttestation V)) (row : NamedAttestation V)
    (hrow : row ∈ rows) (hoff : row ∉ chainRows parent)
    (hunique : ∀ b ∈ rows,
      b.val_index = row.val_index → b.round = row.round → b = row) :
    row ∈ proposalRows parent rows := by
  apply mem_capPerSigner_of_unique
  · exact (mem_exclude_on_chain parent rows row).mpr ⟨hrow, hoff⟩
  · intro b hb hval hround
    have hsource := (mem_exclude_on_chain parent rows b).mp hb
    exact hunique b hsource.1 hval hround


#print axioms processed_rows_erasure
#print axioms selected_source_exact
#print axioms ordered_bodies_mem
#print axioms mem_carried_rows
#print axioms mem_exclude_on_chain
#print axioms mem_capPerSigner
#print axioms mem_capPerSigner_of_unique
#print axioms mem_proposalRows
#print axioms mem_proposalRows_of_unique
end DecoupledConsensusModel.Proofs.NamedProposalRows

end
