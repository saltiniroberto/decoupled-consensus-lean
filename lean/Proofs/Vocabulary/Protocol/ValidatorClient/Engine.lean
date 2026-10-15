module
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Model.Vocabulary.Protocol.Evidence
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Pairs
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights
import Proofs.Vocabulary.ModelVocabulary.FinalityGadget.ChainState
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.ChainState.Evidence
import Mathlib.Tactic.ENatToNat

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace Engine

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Vote selectivity -/


section Gating

variable {Λ : Record}

omit [Fintype V] [DecidableEq V] in
/-- `height_pair` returns the empty pair, or the height fields are `some (h, T, ν)` and it returns
    `timeout h` or `target h T`. -/
theorem height_pair_cases (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) :
    Protocol.height_pair Λ fields fp = .empty ∨
      ∃ (h : Height) (T : BlockId) (ν : Bool), fields = some (h, T, ν) ∧
        (Protocol.height_pair Λ fields fp = .timeout h ∨
          Protocol.height_pair Λ fields fp = .target h T) := by
  cases fields with
  | none => exact Or.inl rfl
  | some f =>
    obtain ⟨h, T, ν⟩ := f
    have key : Protocol.height_pair Λ (some (h, T, ν)) fp = .empty ∨
        Protocol.height_pair Λ (some (h, T, ν)) fp = .timeout h ∨
        Protocol.height_pair Λ (some (h, T, ν)) fp = .target h T := by
      dsimp only [Protocol.height_pair]
      repeat' split
      all_goals
        first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
    rcases key with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h, T, ν, rfl, h0⟩


omit [Fintype V] [DecidableEq V] in
/-- An emitted target pair `target h T` comes from height fields `some (h, T, ν)`. -/
theorem height_pair_target_gated {fields : Option (Height × BlockId × Bool)}
    {fp : Option FinalityPair} {h : Height} {T : BlockId}
    (hp : Protocol.height_pair Λ fields fp = .target h T) :
    ∃ ν : Bool, fields = some (h, T, ν) := by
  rcases height_pair_cases (Λ := Λ) fields fp with hc | ⟨h', T', ν, hf, hc | hc⟩
  · exact absurd (hp ▸ hc) (by simp)
  · exact absurd (hc ▸ hp) (by simp)
  · obtain ⟨rfl, rfl⟩ := HeightPair.target.injEq .. ▸ (hc ▸ hp : _)
    exact ⟨ν, hf⟩

omit [Fintype V] [DecidableEq V] in
/-- An emitted nonempty pair of height `h` comes from height fields with height `h`. -/
theorem height_pair_height_gated {fields : Option (Height × BlockId × Bool)}
    {fp : Option FinalityPair} {h : Height}
    (hp : (Protocol.height_pair Λ fields fp).height? = some h) :
    ∃ (T : BlockId) (ν : Bool), fields = some (h, T, ν) := by
  rcases height_pair_cases (Λ := Λ) fields fp with hc | ⟨h', T', ν, hf, hc | hc⟩
  · rw [hc] at hp; exact absurd hp (by simp [HeightPair.height?])
  · rw [hc] at hp
    simp only [HeightPair.height?, Option.some_inj] at hp
    exact ⟨T', ν, hp ▸ hf⟩
  · rw [hc] at hp
    simp only [HeightPair.height?, Option.some_inj] at hp
    exact ⟨T', ν, hp ▸ hf⟩

end Gating


section GradedGate

omit [Fintype V] in
/-- The unique-choice picker returns a member of its own set. -/
theorem pickUnique?_mem {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {x : α} (h : pickUnique? T p = some x) : x ∈ T := by
  unfold pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact Finset.choose_mem _ _ hex
  · exact absurd h (by simp)

omit [Fintype V] in
/-- `Block.deepest?` returns a member of its tree. -/
theorem deepest?_mem {T : Finset (Block V)} {B : Block V}
    (h : Block.deepest? T = some B) : B ∈ T :=
  pickUnique?_mem h

omit [Fintype V] in
/-- Every member of `chain_up n B` is an ancestor of `B`. -/
theorem mem_chain_up_preceq : ∀ (n : Nat) (B X : Block V),
    X ∈ Protocol.chain_up n B → Block.preceq X B = true := by
  intro n
  induction n with
  | zero =>
      intro B X h
      simp only [Protocol.chain_up, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact Block.preceq_self _
  | succ n ih =>
      intro B X h
      cases B with
      | genesis =>
          simp only [Protocol.chain_up, Block.parent?, List.mem_cons, List.not_mem_nil,
            or_false] at h
          subst h
          exact Block.preceq_self _
      | node p s r gv gsv ats i =>
          simp only [Protocol.chain_up, Block.parent?, List.mem_cons] at h
          rcases h with rfl | h
          · exact Block.preceq_self _
          · simp only [Block.preceq, Bool.or_eq_true]
            exact Or.inr (ih p X h)

omit [Fintype V] in
/-- Every member of `chain_of C` is an ancestor of `C`. -/
theorem mem_chain_of_preceq {C X : Block V} (h : X ∈ Protocol.chain_of C) :
    Block.preceq X C = true :=
  mem_chain_up_preceq _ _ _ h

omit [Fintype V] in
/-- The block `deepest_clear` returns is an ancestor of the block `C` it was given. -/
theorem deepest_clear_preceq {floor : Option (Block V)} {C B : Block V}
    {test : Block V → Bool} (h : Protocol.deepest_clear floor C test = some B) :
    Block.preceq B C = true := by
  unfold Protocol.deepest_clear at h
  have hmem := deepest?_mem h
  exact mem_chain_of_preceq (List.mem_toFinset.mp (Finset.mem_filter.mp hmem).1)


open Protocol (GradeContract)


end GradedGate


end Engine
end Proofs
end DecoupledConsensusModel

end
