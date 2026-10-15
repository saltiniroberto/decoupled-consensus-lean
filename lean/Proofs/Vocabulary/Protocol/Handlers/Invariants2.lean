module
public import Proofs.Vocabulary.Protocol.Handlers.Invariants
public import Model.Vocabulary.Protocol.Evidence

@[expose] public section

/-!
# Store invariants by induction

The store invariants that need an induction over reachable stores, and the finality invariant
`ChainFinality` of a chain state.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record HeightId)
open Protocol (HealConfig)
open Internal

/-! ## Ancestry and the justification order -/

section Ancestry

variable {V : Type} [DecidableEq V]

/-- Genesis precedes every block. -/
theorem preceq_genesis (B : Block V) : Block.preceq Block.genesis B = true := by
  induction B with
  | genesis => simp [Block.preceq]
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr ih

/-- A block's parent precedes it; genesis is its own parent. -/
theorem preceq_parent (B : Block V) : Block.preceq B.parent B = true := by
  cases B with
  | genesis => exact Block.preceq_self _
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent, Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self _)

omit [DecidableEq V] in
/-- `B.parent` is `P` when `B.parent? = some P`. -/
theorem parent_eq_of_parent? {B P : Block V} (h : B.parent? = some P) :
    B.parent = P := by
  cases B with
  | genesis => simp [Block.parent?] at h
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent?, Option.some.injEq] at h
      simpa only [Block.parent] using h

end Ancestry

/-- In the justification order, a smaller identifier has a smaller or equal height. -/
theorem heightId_height_le_of_le {a b : HeightId} (h : a ≤ b) :
    a.height ≤ b.height := by
  have h' : toLex (a.height, a.id) ≤ toLex (b.height, b.id) := h
  exact (Prod.Lex.toLex_le_toLex'.mp h').1


/-! ## The finality invariant of a chain state -/

section ChainStateInvariant

variable {V : Type} [DecidableEq V]

/-- The finality invariant of a chain state: `F ⪯ J ⪯ T_h ⪯ L`, `h_F ≤ h_j` and `h_j < h`. -/
structure ChainFinality (σ : ChainState V) : Prop where
  /-- The height target `T_h` precedes the latest block `L`. -/
  target_preceq_latest : Block.preceq σ.T_h σ.L = true
  /-- The justified block `J` precedes the height target `T_h`. -/
  justified_preceq_target : Block.preceq σ.J σ.T_h = true
  /-- The finalized block `F` precedes the justified block `J`. -/
  finalized_preceq_justified : Block.preceq σ.F σ.J = true
  /-- The finalized height `h_F` is at most the justified height `h_j`. -/
  heights_ordered : σ.h_F ≤ σ.h_j
  /-- The justified height `h_j` is less than the current height `h`. -/
  justified_below_height : σ.h_j < σ.h

/-- The initial chain state satisfies `ChainFinality`. -/
theorem chainFinality_initial : ChainFinality (ChainState.initial : ChainState V) :=
  { target_preceq_latest := Block.preceq_self _
    justified_preceq_target := Block.preceq_self _
    finalized_preceq_justified := Block.preceq_self _
    heights_ordered := Nat.le_refl 0
    justified_below_height := Nat.zero_lt_one }


variable [Fintype V]

/-- `process_height_events` preserves `ChainFinality`. -/
theorem chainFinality_process_height_events (E : Env V) (cfg : HeightConfig)
    (σ : ChainState V) (h : ChainFinality σ) :
    ChainFinality (Protocol.process_height_events E cfg σ) := by
  simp only [Protocol.process_height_events, Protocol.advance_height]
  split_ifs
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target := h.target_preceq_latest
        finalized_preceq_justified := h.justified_preceq_target
        heights_ordered := Nat.le_of_lt h.justified_below_height
        justified_below_height := Nat.lt_succ_self _ }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target :=
          Block.preceq_trans h.justified_preceq_target h.target_preceq_latest
        finalized_preceq_justified := Block.preceq_self _
        heights_ordered := Nat.le_refl _
        justified_below_height := Nat.lt_succ_of_lt h.justified_below_height }
  · exact
      { target_preceq_latest := h.target_preceq_latest
        justified_preceq_target := h.justified_preceq_target
        finalized_preceq_justified := Block.preceq_self _
        heights_ordered := Nat.le_refl _
        justified_below_height := h.justified_below_height }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target := h.target_preceq_latest
        finalized_preceq_justified :=
          Block.preceq_trans h.finalized_preceq_justified h.justified_preceq_target
        heights_ordered :=
          Nat.le_of_lt (Nat.lt_of_le_of_lt h.heights_ordered h.justified_below_height)
        justified_below_height := Nat.lt_succ_self _ }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target :=
          Block.preceq_trans h.justified_preceq_target h.target_preceq_latest
        finalized_preceq_justified := h.finalized_preceq_justified
        heights_ordered := h.heights_ordered
        justified_below_height := Nat.lt_succ_of_lt h.justified_below_height }
  · exact h


end ChainStateInvariant

/-! ## The store's state map and its finality fields -/

section StoreInvariant

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every entry `m C` of the state map has its latest block preceding `C` and satisfies
    `ChainFinality`. -/
def ChainStatesOk (m : Block V → ChainState V) : Prop :=
  ∀ C : Block V, Block.preceq (m C).L C = true ∧ ChainFinality (m C)

omit [Fintype V] in
/-- The constant map to the initial chain state satisfies `ChainStatesOk`. -/
theorem chainStatesOk_const_initial :
    ChainStatesOk (fun _ : Block V => (ChainState.initial : ChainState V)) :=
  fun C => ⟨preceq_genesis C, chainFinality_initial⟩


/-- The step from `st` to `st'` keeps the state map, `F`, `J` and `h_j`. -/
structure CoreEq (st st' : Protocol.Store V) : Prop where
  /-- The state map is unchanged. -/
  σ_eq : st'.σ = st.σ
  /-- `Σ.F` is unchanged. -/
  F_eq : st'.F = st.F
  /-- `Σ.J` is unchanged. -/
  J_eq : st'.J = st.J
  /-- `Σ.h_j` is unchanged. -/
  h_j_eq : st'.h_j = st.h_j

namespace CoreEq

omit [DecidableEq V] [Fintype V] in
/-- `CoreEq` is reflexive. -/
theorem refl' (st : Protocol.Store V) : CoreEq st st :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `CoreEq` is transitive. -/
theorem trans' {a b c : Protocol.Store V} (h₁ : CoreEq a b) (h₂ : CoreEq b c) :
    CoreEq a c :=
  ⟨h₂.σ_eq.trans h₁.σ_eq, h₂.F_eq.trans h₁.F_eq,
    h₂.J_eq.trans h₁.J_eq, h₂.h_j_eq.trans h₁.h_j_eq⟩

end CoreEq

omit [Fintype V] in
/-- `on_goldfish_vote` satisfies `CoreEq`. -/
theorem coreEq_on_goldfish_vote (st : Protocol.Store V) (vote : GoldfishVote V) :
    CoreEq st (Protocol.on_goldfish_vote st vote) := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `on_goldfish_vote_checked` satisfies `CoreEq`. -/
theorem coreEq_on_goldfish_vote_checked (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    CoreEq st (Protocol.on_goldfish_vote_checked E st vote) := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact coreEq_on_goldfish_vote st vote
  · exact CoreEq.refl' st


/-- A fold of `on_goldfish_vote_checked` satisfies `CoreEq`. -/
theorem coreEq_foldl_on_goldfish_vote_checked (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    CoreEq st (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l generalizing st with
  | nil => exact CoreEq.refl' _
  | cons v vs ih =>
      rw [List.foldl_cons]
      exact CoreEq.trans' (coreEq_on_goldfish_vote_checked E st v) (ih _)

omit [Fintype V] in
/-- `on_sg_vote` satisfies `CoreEq`. -/
theorem coreEq_on_sg_vote (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : CoreEq st (Protocol.on_sg_vote hc st a) := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### The core fields, one at a time -/


omit [Fintype V] in
/-- `update_finality` leaves the state map unchanged. -/
theorem update_finality_σ (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).σ = st.σ := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

/-! ### `Σ.F ⪯ Σ.J` at `update_finality` -/

omit [Fintype V] in
/-- `update_finality` preserves `Σ.F ⪯ Σ.J`. -/
theorem update_finality_preceq (st : Protocol.Store V) (σ : ChainState V)
    (h : Block.preceq st.F st.J = true) :
    Block.preceq (Protocol.update_finality st σ).F
      (Protocol.update_finality st σ).J = true := by
  simp only [Protocol.update_finality]
  split_ifs with h₁ h₂ h₃
  · rw [Bool.and_eq_true, Bool.and_eq_true] at h₂
    exact h₂.1.2
  · rw [Bool.and_eq_true] at h₁
    exact h₁.1
  · rw [Bool.and_eq_true, Bool.and_eq_true] at h₃
    exact h₃.1.2
  · exact h

/-! ### The justification order -/


omit [Fintype V] in
/-- `update_finality` never lowers the justification identifier `(Σ.h_j, Σ.J.root)` in the
    justification order. -/
theorem update_finality_heightId (st : Protocol.Store V) (σ : ChainState V) :
    HeightId.mk st.h_j st.J.root ≤
      HeightId.mk (Protocol.update_finality st σ).h_j
        (Protocol.update_finality st σ).J.root := by
  simp only [Protocol.update_finality]
  split_ifs with h₁ h₂ h₃ <;>
    first
      | exact le_refl _
      | (rw [Bool.and_eq_true, decide_eq_true_eq] at h₁; exact le_of_lt h₁.2)

end StoreInvariant


variable {V : Type} [DecidableEq V] [Fintype V]

end Proofs
end DecoupledConsensusModel

end
