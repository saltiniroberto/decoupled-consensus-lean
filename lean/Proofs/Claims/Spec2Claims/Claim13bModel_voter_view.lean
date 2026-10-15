import Model.Vocabulary.Protocol.ForkChoice.Views
import Model.Vocabulary.Protocol.Store
import Proofs.Claims.ModelIrreducible

/-!
# Facts on `Protocol.voter_view` and `Protocol.voter_support_view`

The two voter views of a Goldfish store at slot `s`. Each is the union of the slot-`(s − 1)` votes
stamped before the view freeze of slot `s − 1`, and the slot-`(s − 1)` votes included in the
slot-`s` blocks of the store's tree.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.find?
  DecoupledConsensusModel.Protocol.GoldfishStore.pool
  DecoupledConsensusModel.Protocol.GoldfishStore.tau
  DecoupledConsensusModel.Protocol.Store.toHealing DecoupledConsensusModel.Protocol.resolution_time
  DecoupledConsensusModel.Protocol.voter_support_view DecoupledConsensusModel.Protocol.voter_view
  DecoupledConsensusModel.beforeCutoff DecoupledConsensusModel.occurrenceMax
  DecoupledConsensusModel.pickUnique? DecoupledConsensusModel.stampedBefore

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A vote in the slot-`s` raw voter view of `gs` is either in `gs.pool (s − 1)` with a stamp
    strictly before the view freeze of slot `s − 1`, or a slot-`(s − 1)` vote included in a slot-`s`
    block of `gs.T`. -/
theorem voter_view_cases (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {u : GoldfishVote V} (h : u ∈ Protocol.voter_view E gs s) :
    (u ∈ gs.pool (s - 1) ∧ ∃ τ : Stamp, gs.timestamp_vote u = some τ ∧
        τ < ((Protocol.view_freeze E (s - 1) : Int) : Stamp)) ∨
      ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1 := by
  simp only [Protocol.voter_view, Finset.mem_union, beforeCutoff, Finset.mem_filter,
    Finset.mem_biUnion, List.mem_toFinset] at h
  rcases h with ⟨hu, hst⟩ | ⟨X, hX, hu, hus⟩
  · refine Or.inl ⟨hu, ?_⟩
    simp only [stampedBefore] at hst
    cases hτ : gs.timestamp_vote u with
    | none => rw [hτ] at hst; simp at hst
    | some τ =>
      rw [hτ] at hst
      exact ⟨τ, rfl, of_decide_eq_true hst⟩
  · exact Or.inr ⟨X, hX.1, hX.2, hu, hus⟩

/-- A slot-`(s − 1)` vote included in a slot-`s` block of `gs.T` is in the slot-`s` raw voter view
    of `gs`. -/
theorem mem_voter_view_of_carried (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {u : GoldfishVote V} {X : Block V} (hX : X ∈ gs.T) (hXs : X.slot = s)
    (hu : u ∈ X.gf_votes) (hus : u.slot = s - 1) :
    u ∈ Protocol.voter_view E gs s := by
  simp only [Protocol.voter_view, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset]
  exact Or.inr ⟨X, ⟨hX, hXs⟩, hu, hus⟩

/-- A vote in the slot-`s` support voter view of `gs` is either in `gs.pool (s − 1)`, with its head
    resolving in `gs.T` to a block of a slot at most the vote's, and both the vote's stamp and that
    block's stamp strictly before the view freeze of slot `s − 1`; or a slot-`(s − 1)` vote of the
    support list of a slot-`s` block of `gs.T`, resolved in `gs.T`. -/
theorem voter_support_view_cases (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {u : GoldfishVote V} (h : u ∈ Protocol.voter_support_view E gs s) :
    (u ∈ gs.pool (s - 1) ∧ ∃ X : Block V, Block.find? gs.T u.head = some X ∧
        X.slot ≤ u.slot ∧ ∃ τ σ : Stamp, gs.timestamp_vote u = some τ ∧
          gs.timestamp_block X = some σ ∧
          τ < ((Protocol.view_freeze E (s - 1) : Int) : Stamp) ∧
          σ < ((Protocol.view_freeze E (s - 1) : Int) : Stamp)) ∨
      ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_support_votes ∧
        Protocol.resolved gs.T u = true ∧ u.slot = s - 1 := by
  simp only [Protocol.voter_support_view, Finset.mem_union, beforeCutoff, Finset.mem_filter,
    Finset.mem_biUnion, List.mem_toFinset] at h
  rcases h with ⟨hu, hst⟩ | ⟨X, hX, hu, hres, hus⟩
  · refine Or.inl ⟨hu, ?_⟩
    simp only [stampedBefore, Protocol.GoldfishStore.tau, Protocol.resolution_time] at hst
    cases hf : Block.find? gs.T u.head with
    | none => simp [hf] at hst
    | some X =>
      simp only [hf] at hst
      by_cases hXs : X.slot ≤ u.slot
      · simp only [if_pos hXs] at hst
        cases hτ : gs.timestamp_vote u with
        | none => simp [hτ, occurrenceMax] at hst
        | some τ =>
          cases hσ : gs.timestamp_block X with
          | none => simp [hτ, hσ, occurrenceMax] at hst
          | some σ =>
            simp only [hτ, hσ, occurrenceMax, decide_eq_true_eq, max_lt_iff] at hst
            exact ⟨X, rfl, hXs, τ, σ, rfl, hσ, hst.1, hst.2⟩
      · simp [if_neg hXs] at hst
  · exact Or.inr ⟨X, hX.1, hX.2, hu, hres, hus⟩

/-- A slot-`(s − 1)` vote of the support list of a slot-`s` block of `gs.T`, resolved in `gs.T`, is
    in the slot-`s` support voter view of `gs`. -/
theorem mem_voter_support_view_of_carried (E : Env V) (gs : Protocol.GoldfishStore V)
    (s : Slot) {u : GoldfishVote V} {X : Block V} (hX : X ∈ gs.T) (hXs : X.slot = s)
    (hu : u ∈ X.gf_support_votes) (hres : Protocol.resolved gs.T u = true)
    (hus : u.slot = s - 1) :
    u ∈ Protocol.voter_support_view E gs s := by
  simp only [Protocol.voter_support_view, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset]
  exact Or.inr ⟨X, ⟨hX, hXs⟩, hu, hres, hus⟩

/-- The raw voter view does not read the store's clock or slot: setting `t` and `s` in `st` leaves
    its slot-`k` raw voter view unchanged. -/
theorem voter_view_set_clock_slot (E : Env V) (st : Protocol.Store V) (t : Int) (s k : Slot) :
    Protocol.voter_view E
        ({ st with t := t, s := s } : Protocol.Store V).toHealing.toFG.toSG.toGoldfishStore k
      = Protocol.voter_view E st.toHealing.toFG.toSG.toGoldfishStore k := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A vote of the slot-`s` raw voter view of `gs` is either in the cutoff view of `gs.pool (s − 1)`
    at the view freeze of slot `s − 1`, or a slot-`(s − 1)` vote included in a slot-`s` block of
    `gs.T`. -/
theorem voter_view_cases_beforeCutoff (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {u : GoldfishVote V} (h : u ∈ Protocol.voter_view E gs s) :
    u ∈ beforeCutoff gs.timestamp_vote (Protocol.view_freeze E (s - 1)) (gs.pool (s - 1)) ∨
      ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1 := by
  simp only [Protocol.voter_view, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset] at h
  rcases h with h | ⟨X, ⟨hX, hXs⟩, hu, hus⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, hX, hXs, hu, hus⟩

end DecoupledConsensusModel.Sts
