module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
import Mathlib.Tactic.ENatToNat
public import Model.Vocabulary.Statements.Instantiation.Certificates
public import Mathlib.Data.DFinsupp.Notation
public import Mathlib.Data.Finsupp.Notation
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Block emissions

The shape of the blocks that proposal ticks emit, and that an honest validator emits at most one
block per slot.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block a tick of `v` at `t` emits is its proposal: `t` is the proposal time of a slot greater
    than 0 whose proposer is `v`, and the block is the output of the named proposal duty on the
    tick's prepared read. -/
theorem block_mem_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {B : NamedBlock V} (h : Object.block B ∈ (on_tick_emit S v n t).2) :
    (0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = v) ∧
      (Protocol.NamedDuties.propose_block_with
          (NamedProfile.gradeContract (NamedActionReads.confirmationReadFrom S n t).cache)
          S.E S.hc S.cfg (S.node v)
          (NamedActionReads.confirmationReadFrom S n t).st).2 = some B := by
  have hiteP : ∀ (P : Prop) (inst : Decidable P) (a₁ a₂ : Protocol.NamedStore V)
      (b₁ b₂ : Protocol.NamedRecord) (l₁ l₂ : List (Object V)),
      Object.block B ∈ (@ite _ P inst (a₁, b₁, l₁) (a₂, b₂, l₂)).2.2 →
        Object.block B ∈ l₁ ∨ Object.block B ∈ l₂ := by
    intro P inst a₁ a₂ b₁ b₂ l₁ l₂ hm
    by_cases hP : P
    · rw [if_pos hP] at hm; exact Or.inl hm
    · rw [if_neg hP] at hm; exact Or.inr hm
  have hsplit : ∀ l₁ l₂ l₃ : List (Object V), Object.block B ∈ l₁ ++ l₂ ++ l₃ →
      Object.block B ∈ l₁ ∨ Object.block B ∈ l₂ ∨ Object.block B ∈ l₃ := by
    intro l₁ l₂ l₃ hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock] at h ⊢
  rcases hiteP _ _ _ _ _ _ _ _ h with hm | hm
  · rcases hsplit _ _ _ hm with hm | hm | hm
    · split at hm
      · split at hm
        · exact absurd hm (by simp)
        · rename_i hg _hopt B' heq
          simp only [List.mem_singleton] at hm
          injection hm with hm'
          exact ⟨by rwa [S.node_val_index] at hg, by rw [heq, hm']⟩
      · exact absurd hm (by simp)
    · exact absurd hm (by simp [List.mem_ite_nil_right])
    · exact absurd hm (by simp)
  · rcases List.mem_append.mp hm with hm | hm
    · split at hm
      · split at hm
        · exact absurd hm (by simp)
        · rename_i hg _hopt B' heq
          simp only [List.mem_singleton] at hm
          injection hm with hm'
          exact ⟨by rwa [S.node_val_index] at hg, by rw [heq, hm']⟩
      · exact absurd hm (by simp)
    · exact absurd hm (by simp [List.mem_ite_nil_right])

/-- A block the named proposal duty returns has the store's slot. -/
theorem propose_block_with_slot (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) {B : NamedBlock V}
    (hB : (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B) :
    B.slot = st.core.s := by
  have hp : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st = some B := by
    simp only [Protocol.NamedDuties.propose_block_with] at hB
    revert hB
    cases Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st <;> exact id
  simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
    Option.map_eq_some_iff] at hp
  obtain ⟨parent, -, hBeq⟩ := hp
  rw [← hBeq]
  rfl

/-- A block that `u` emits at `t` has a slot greater than 0, `t` is that slot's proposal time, and
    `u` is that slot's proposer. -/
theorem emits_block_shape (S : Setup V) (ρ : Run V) {u : V} {B : NamedBlock V} {t : Time}
    (h : ρ.emits S u (Object.block B) t) :
    0 < B.slot ∧ t = Protocol.proposal_time S.E B.slot ∧ S.E.proposer B.slot = u := by
  obtain ⟨i, -, hmem⟩ := h
  obtain ⟨⟨hpos, htime, hprop⟩, hB⟩ :=
    block_mem_on_tick_emit S u (ρ.stateBefore S i u) t hmem
  have hslot : B.slot = S.E.slotOf t := by
    have hB' := propose_block_with_slot _ S.E S.hc S.cfg (S.node u) _ hB
    rwa [ModelProperties.confirmationReadFrom_st_core_s] at hB'
  refine ⟨by rw [hslot]; exact hpos, by rw [hslot]; exact htime, ?_⟩
  rw [hslot]; exact hprop

omit [DecidableEq V] [Fintype V] in
/-- A duplicate-free list positions each element once. -/
theorem index_unique_of_nodup {α : Type} {l : List α} (hnd : l.Nodup) {i j : Nat}
    {a : α} (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hilt, hiv⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjlt, hjv⟩ := List.getElem?_eq_some_iff.mp hj
  exact hnd.getElem_inj_iff.mp (hiv.trans hjv.symm)

/-- Two blocks of the same slot emitted by `u` are equal. -/
theorem emits_block_unique (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {u : V} {B B' : NamedBlock V} {t t' : Time}
    (h : ρ.emits S u (Object.block B) t) (h' : ρ.emits S u (Object.block B') t')
    (hs : B.slot = B'.slot) : B = B' := by
  have ht := (emits_block_shape S ρ h).2.1
  have ht' := (emits_block_shape S ρ h').2.1
  have hteq : t = t' := by rw [ht, ht', hs]
  subst hteq
  obtain ⟨i, hi, hmem⟩ := h
  obtain ⟨j, hj, hmem'⟩ := h'
  have hij : i = j := index_unique_of_nodup (NamedScheduleWellFormed.nodup sch) hi hj
  subst hij
  have heq := (block_mem_on_tick_emit S u (ρ.stateBefore S i u) t hmem).2
  have heq' := (block_mem_on_tick_emit S u (ρ.stateBefore S i u) t hmem').2
  rw [heq] at heq'
  exact Option.some_inj.mp heq'

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
