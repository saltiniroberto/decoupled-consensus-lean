module
public import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
public import Proofs.Vocabulary.Protocol.Handlers.Invariants2
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
public import Proofs.Vocabulary.Internal.ModelVocabulary.FGForkChoice.Finality

@[expose] public section

/-!
# Record writers and fork-choice membership lemmas

Read-back lemmas for `Λ.with_lock` and the invariant `LockCompatible`; the facts that a
parent-closed tree holds every ancestor of its members and that `update_finality` writes `Σ.J` from
its chain state or not at all; and the facts that GHOST walks stay in their tree and that the
filtered block tree is a subset of `Σ.T` whose members descend from the FG root.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Records

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal

/-! ## The record writers -/


/-- `Λ.with_lock h T` reads back `T` at `h`. -/
theorem with_lock_self (Λ : Record) (h : Height) (T : BlockId) :
    (Λ.with_lock h T).lock h = some T := by
  simp [Protocol.Record.with_lock]

/-- `Λ.with_lock h T` leaves the lock at every other height unchanged. -/
theorem with_lock_ne {Λ : Record} {h k : Height} {T : BlockId} (hk : k ≠ h) :
    (Λ.with_lock h T).lock k = Λ.lock k := by
  simp [Protocol.Record.with_lock, hk]


/-- A record in which every lock `Λ.lock h = some T` comes with no timeout at `h` and a target at
    `h` that is empty or `T`. -/
def LockCompatible (Λ : Record) : Prop :=
  ∀ (h : Height) (T : BlockId), Λ.lock h = some T →
    Λ.timeout h = false ∧ (Λ.target h = none ∨ Λ.target h = some T)

/-- The initial record satisfies `LockCompatible`. -/
theorem lockCompatible_initial : LockCompatible Record.initial := by
  intro h T hl
  simp [Protocol.Record.initial] at hl


section DerivedChain

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Parent-closed trees -/

omit [Fintype V] in
/-- A parent-closed tree holds every ancestor of each of its members. -/
theorem mem_of_preceq {T : Finset (Block V)}
    (hcl : ∀ B ∈ T, B.parent? = none ∨ B.parent ∈ T) :
    ∀ (X B : Block V), B ∈ T → Block.preceq X B = true → X ∈ T := by
  intro X B
  induction B with
  | genesis =>
      intro hB hp
      simp only [Block.preceq, decide_eq_true_eq] at hp
      exact hp ▸ hB
  | node p s r gv gsv ats i ih =>
      intro hB hp
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hp
      rcases hp with rfl | hp
      · exact hB
      · refine ih ?_ hp
        rcases hcl _ hB with hn | hpar
        · simp [Block.parent?] at hn
        · simpa [Block.parent] using hpar


end DerivedChain

section StoreJustified

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `update_finality` leaves `Σ.J` unchanged or sets it to the given chain state's `J`. -/
theorem update_finality_J_cases (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).J = st.J ∨
      (Protocol.update_finality st σ).J = σ.J := by
  simp only [Protocol.update_finality]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

end StoreJustified

/-! ## Fork-choice walks stay in the processed tree -/

section Head

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A fuelled GHOST walk returns the block it started from or a member of its tree. -/
theorem ghost_walk_mem (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    ∀ (n : Nat) (H : Block V),
      Protocol.ghost_walk tree score eligible n H = H ∨
        Protocol.ghost_walk tree score eligible n H ∈ tree := by
  intro n
  induction n with
  | zero => intro H; exact Or.inl rfl
  | succ n ih =>
      intro H
      rw [Protocol.ghost_walk]
      split
      · exact Or.inl rfl
      · rename_i C hstep
        have hmem : C ∈ Protocol.ghost_children tree eligible H :=
          Proofs.Engine.pickUnique?_mem hstep
        rw [Protocol.ghost_children, Finset.mem_filter] at hmem
        rcases ih C with h | h
        · rw [h]
          exact Or.inr hmem.1
        · exact Or.inr h

omit [Fintype V] in
/-- `ghost` returns its anchor or a member of its tree. -/
theorem ghost_mem (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    Protocol.ghost anchor tree score eligible = anchor ∨
      Protocol.ghost anchor tree score eligible ∈ tree :=
  ghost_walk_mem tree score eligible tree.card anchor

omit [Fintype V] in
/-- A `ghost` walk whose anchor is in `T` and whose tree is a subset of `T` returns a member of `T`. -/
theorem ghost_mem_of {T : Finset (Block V)} {anchor : Block V}
    {tree : Finset (Block V)} (score : Block V → Nat) (eligible : Block V → Bool)
    (hanchor : anchor ∈ T) (htree : tree ⊆ T) :
    Protocol.ghost anchor tree score eligible ∈ T := by
  rcases ghost_mem anchor tree score eligible with h | h
  · rw [h]
    exact hanchor
  · exact htree h

omit [Fintype V] in
/-- The filtered block tree is a subset of the processed tree. -/
theorem get_filtered_block_tree_subset (st : Protocol.FGStore V) :
    Protocol.get_filtered_block_tree st ⊆ st.T := by
  intro B hB
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Finset.mem_filter] at hB
  exact hB.1.1.1

omit [Fintype V] in
/-- `get_filtered_block_tree_from st blocks` is a subset of `blocks`. -/
theorem get_filtered_block_tree_from_subset (st : Protocol.FGStore V)
    (blocks : Finset (Block V)) :
    Protocol.get_filtered_block_tree_from st blocks ⊆ blocks := by
  intro B hB
  simp only [Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Finset.mem_filter] at hB
  exact hB.1.1.1


omit [Fintype V] in

/-- Every member of the filtered block tree is a descendant of the FG root. -/
theorem preceq_get_fg_root_of_mem_filtered {st : Protocol.FGStore V}
    {B : Block V} (hB : B ∈ Protocol.get_filtered_block_tree st) :
    Block.preceq (Protocol.get_fg_root st) B = true := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Finset.mem_filter] at hB
  exact hB.2

omit [Fintype V] in
/-- A block of the viable tree that is a descendant of the FG root is in the filtered block tree. -/
theorem mem_filtered_of_mem_V_tree {st : Protocol.FGStore V} {B : Block V}
    (hB : B ∈ Protocol.V_tree st)
    (hroot : Block.preceq (Protocol.get_fg_root st) B = true) :
    B ∈ Protocol.get_filtered_block_tree st := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Finset.mem_filter]
  exact ⟨hB, hroot⟩


omit [Fintype V] in
/-- If `Σ.F ⪯ Σ.J`, then `Σ.F` is an ancestor of the FG root. -/
theorem preceq_get_fg_root_of_F {st : Protocol.FGStore V}
    (hFJ : Block.preceq st.F st.J = true) :
    Block.preceq st.F (Protocol.get_fg_root st) = true := by
  simp only [Protocol.get_fg_root]
  split
  · exact hFJ
  · exact Block.preceq_self _

omit [Fintype V] in
/-- If `Σ.F ⪯ Σ.J`, `P` is in the filtered block tree, and `R` is a processed ancestor of `P` that
    is a descendant of the FG root, then `R` is in the filtered block tree. -/
theorem mem_filtered_of_preceq {st : Protocol.FGStore V} {P R : Block V}
    (hFJ : Block.preceq st.F st.J = true)
    (hP : P ∈ Protocol.get_filtered_block_tree st) (hRT : R ∈ st.T)
    (hRP : Block.preceq R P = true)
    (hroot : Block.preceq (Protocol.get_fg_root st) R = true) :
    R ∈ Protocol.get_filtered_block_tree st := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Finset.mem_filter, Protocol.viable, decide_eq_true_eq] at hP ⊢
  obtain ⟨⟨⟨-, -⟩, W, hW, hPW, hh⟩, -⟩ := hP
  have hFR : Block.preceq st.F R = true :=
    Block.preceq_trans (preceq_get_fg_root_of_F hFJ) hroot
  exact ⟨⟨⟨hRT, hFR⟩, W, hW, Block.preceq_trans hRP hPW, hh⟩, hroot⟩


end Head

end Records
end Proofs
end DecoupledConsensusModel

end
