import Proofs.Instance.Members.ChainStateToHandlers
import Proofs.Instance.Members.ForkChoiceGrades
import Proofs.Instance.Members.DutiesNode
import Proofs.Instance.NoRaise.Stamps

/-!
# The store and node types of `Model.specDraft`

The subtypes `OkStore V` and `OkNode V` of the stores and node states that meet `StoreOk`, the
outcome sets read through a map (`preimageOutcomes`), the test `RootHeldByOther`, and the lemmas
that the spec's store writers keep `StoreOk`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecDraftRecord

open Spec
open SpecDraftRecord.NoRaise
open scoped DC

/-- The stores that meet `StoreOk`: stamped, with distinct roots, holding the parent of each of
    their blocks, and holding their finalized block. -/
abbrev OkStore (V : Type) : Type := {st : Store V // StoreOk st}

/-- The node states whose store meets `StoreOk`. -/
abbrev OkNode (V : Type) : Type := {n : NodeState V // StoreOk n.st}

/-- The outcomes `x` whose image `Except.map g x` is an outcome of `m`. -/
def preimageOutcomes {α β : Type} (g : β → α) (m : DC.NDRE α) : DC.NDRE β :=
  ExceptT.mk {x | Except.map g x ∈ m.run}

/-- `preimageOutcomes g m` returns `b` exactly when `m` returns `g b`. -/
theorem returns_preimageOutcomes {α β : Type} (g : β → α) (m : DC.NDRE α) (b : β) :
    DecoupledConsensusModel.Sts.Record.Returns (preimageOutcomes g m) b ↔
      DecoupledConsensusModel.Sts.Record.Returns m (g b) := Iff.rfl

/-- Some block of the tree `T` other than `B` has `B`'s root. -/
def RootHeldByOther {V : Type} (T : Finset (Block V)) (B : Block V) : Prop :=
  ∃ B' ∈ T, B' ≠ B ∧ B'.root = B.root

instance {V : Type} [DecidableEq V] (T : Finset (Block V)) (B : Block V) :
    Decidable (RootHeldByOther T B) := by
  unfold RootHeldByOther
  infer_instance

/-- The object `o` is a block `B` and some block of the tree `T` other than `Block.toSpecNamed B`
    has its root. -/
def objectRootHeldByOther {V : Type} (T : Finset (Block V)) :
    DecoupledConsensusModel.Execution.NamedObject V → Prop
  | .block B => RootHeldByOther T (Block.toSpecNamed B)
  | .gfVote _ => False
  | .attest _ => False

instance {V : Type} [DecidableEq V] (T : Finset (Block V))
    (o : DecoupledConsensusModel.Execution.NamedObject V) :
    Decidable (objectRootHeldByOther T o) := by
  cases o <;> unfold objectRootHeldByOther <;> infer_instance

/-- Every block of the tree `st.T` has a stamp, no two distinct blocks of the tree share a root, the
    tree holds the parent of each of its blocks, and the tree holds `st.F`. -/
def TreeOk {V : Type} (st : Store V) : Prop :=
  (∀ B ∈ st.T, st.timestamp_block B ≠ none) ∧ DistinctRoots st.T ∧ ParentClosed st.T ∧
    st.F ∈ st.T

instance {V : Type} [DecidableEq V] (st : Store V) : Decidable (TreeOk st) := by
  unfold TreeOk DistinctRoots ParentClosed
  infer_instance

namespace OkStore

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The initial store meets `StoreOk`. -/
theorem init : StoreOk (Store.init : Store V) := by
  refine ⟨stamped_init, ?_, ?_, ?_⟩
  · intro B hB B' hB' _
    simp only [Store.init, Finset.mem_singleton] at hB hB'
    rw [hB, hB']
  · intro B hB
    simp only [Store.init, Finset.mem_singleton] at hB
    subst hB
    simp [Store.init, Block.parent]
  · simp [Store.init]

/-! ## Writers that keep the tree -/

/-- A store whose stamps are kept (`Frame`) and whose tree and finalized block are unchanged meets
    `StoreOk` when the store it came from does. -/
theorem of_frame {st st' : Store V} (h : StoreOk st) (hf : Frame st st') (hT : st'.T = st.T)
    (hF : st'.F = st.F) : StoreOk st' :=
  ⟨hf.1 h.1, hT ▸ h.2.1, hT ▸ h.2.2.1, by rw [hT, hF]; exact h.2.2.2⟩

omit [Fintype V] in
/-- `Protocol.on_goldfish_vote` keeps the tree. -/
theorem on_goldfish_vote_T (st : Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).T = st.T := by
  unfold Protocol.on_goldfish_vote
  simp only [Id.run]
  split_ifs <;> rfl

/-- `Protocol.on_goldfish_vote_checked` keeps the tree. -/
theorem on_goldfish_vote_checked_T (P : Provisional V) (st : Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked P st u).T = st.T := by
  unfold Protocol.on_goldfish_vote_checked
  simp only [Id.run]
  split_ifs <;> first | rfl | exact on_goldfish_vote_T st u

omit [Fintype V] in
/-- `Protocol.admit_attestation` keeps the tree. -/
theorem admit_attestation_T (C : Config) (st : Store V) (a : Attestation V) :
    (Protocol.admit_attestation C st a).T = st.T := by
  unfold Protocol.admit_attestation
  simp only [Id.run]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `Protocol.admit_attestations` keeps the tree. -/
theorem admit_attestations_T (C : Config) (st : Store V) (rows : List (Attestation V)) :
    (Protocol.admit_attestations C st rows).T = st.T := by
  unfold Protocol.admit_attestations
  simp only [Id.run]
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
      simp only [List.forIn_cons]
      exact (ih (Protocol.admit_attestation C st a)).trans (admit_attestation_T C st a)

omit [Fintype V] in
/-- `Protocol.on_goldfish_vote` keeps the finalized block. -/
theorem on_goldfish_vote_F (st : Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).F = st.F := by
  unfold Protocol.on_goldfish_vote
  simp only [Id.run]
  split_ifs <;> rfl

/-- `Protocol.on_goldfish_vote_checked` keeps the finalized block. -/
theorem on_goldfish_vote_checked_F (P : Provisional V) (st : Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked P st u).F = st.F := by
  unfold Protocol.on_goldfish_vote_checked
  simp only [Id.run]
  split_ifs <;> first | rfl | exact on_goldfish_vote_F st u

omit [Fintype V] in
/-- `Protocol.admit_attestation` keeps the finalized block. -/
theorem admit_attestation_F (C : Config) (st : Store V) (a : Attestation V) :
    (Protocol.admit_attestation C st a).F = st.F := by
  unfold Protocol.admit_attestation
  simp only [Id.run]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `Protocol.admit_attestations` keeps the finalized block. -/
theorem admit_attestations_F (C : Config) (st : Store V) (rows : List (Attestation V)) :
    (Protocol.admit_attestations C st rows).F = st.F := by
  unfold Protocol.admit_attestations
  simp only [Id.run]
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
      simp only [List.forIn_cons]
      exact (ih (Protocol.admit_attestation C st a)).trans (admit_attestation_F C st a)

/-- `Protocol.on_goldfish_vote` keeps `StoreOk`. -/
theorem on_goldfish_vote {st : Store V} (h : StoreOk st) (u : GoldfishVote V) :
    StoreOk (Protocol.on_goldfish_vote st u) :=
  of_frame h (frame_on_goldfish_vote st u) (on_goldfish_vote_T st u) (on_goldfish_vote_F st u)

/-- `Protocol.on_goldfish_vote_checked` keeps `StoreOk`. -/
theorem on_goldfish_vote_checked (P : Provisional V) {st : Store V} (h : StoreOk st)
    (u : GoldfishVote V) : StoreOk (Protocol.on_goldfish_vote_checked P st u) :=
  of_frame h (frame_on_goldfish_vote_checked P st u) (on_goldfish_vote_checked_T P st u)
    (on_goldfish_vote_checked_F P st u)

/-- Receiving the Goldfish votes of a list one by one, in order, keeps `StoreOk`. -/
theorem foldl_checked (P : Provisional V) (votes : List (GoldfishVote V)) :
    ∀ {st : Store V}, StoreOk st → StoreOk (votes.foldl (Protocol.on_goldfish_vote_checked P) st) := by
  induction votes with
  | nil => exact fun h => h
  | cons u votes ih => exact fun h => ih (on_goldfish_vote_checked P h u)

/-- `Protocol.admit_attestation` keeps `StoreOk`. -/
theorem admit_attestation (C : Config) {st : Store V} (h : StoreOk st) (a : Attestation V) :
    StoreOk (Protocol.admit_attestation C st a) :=
  of_frame h (frame_admit_attestation C st a) (admit_attestation_T C st a)
    (admit_attestation_F C st a)

/-- `Protocol.admit_attestations` keeps `StoreOk`. -/
theorem admit_attestations (C : Config) {st : Store V} (h : StoreOk st)
    (rows : List (Attestation V)) : StoreOk (Protocol.admit_attestations C st rows) :=
  of_frame h (frame_admit_attestations C st rows) (admit_attestations_T C st rows)
    (admit_attestations_F C st rows)

omit [Fintype V] in
/-- `Handlers.updateFinalityWith` writes only `h_max`, `J`, `h_j` and `F`. -/
theorem updateFinalityWith_shape (st : Store V) (σ : Protocol.ChainState V) :
    ∃ a b c d, Handlers.updateFinalityWith st σ = { st with h_max := a, J := b, h_j := c, F := d } := by
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs <;> exact ⟨_, _, _, _, rfl⟩

omit [Fintype V] in
/-- When the store's finalized block is in the tree, `Handlers.updateFinalityWith` leaves a
    finalized block that is in the tree. -/
theorem updateFinalityWith_F_mem {st : Store V} (hF : st.F ∈ st.T) (σ : Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).F ∈ st.T := by
  have key : ∀ {b c : Bool} {hm}, (b && c &&
      decide (σ.F ∈ Protocol.viable_tree st.σ st.F hm st.T)) = true → σ.F ∈ st.T := by
    intro b c hm h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp h.2).1).1
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs with h1 h2 h3
  · exact key h2
  · exact hF
  · exact key h3
  · exact hF

omit [Fintype V] in
/-- `Handlers.updateFinalityWith` keeps `StoreOk`. -/
theorem updateFinalityWith {st : Store V} (h : StoreOk st) (σ : Protocol.ChainState V) :
    StoreOk (Handlers.updateFinalityWith st σ) := by
  have hmem := updateFinalityWith_F_mem h.2.2.2 σ
  obtain ⟨a, b, c, d, e⟩ := updateFinalityWith_shape st σ
  rw [e] at hmem ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, hmem⟩

omit [Fintype V] in
/-- `Protocol.update_finality` keeps `StoreOk`. -/
theorem update_finality {st : Store V} (h : StoreOk st) (B : Block V) :
    StoreOk (Protocol.update_finality st B) := by
  rw [Handlers.update_finality_eq]
  exact updateFinalityWith h _

/-! ## Writing a block -/

omit [Fintype V] in
/-- Adding a stamped block `B` to the tree of a store meeting `StoreOk`, whatever chain states it
    then holds, keeps `StoreOk` when the tree holds `B`'s parent and no other block of the tree has
    `B`'s root. -/
theorem insert {st : Store V} (h : StoreOk st) {B : Block V} (hpar : B.parent ∈ st.T)
    (hroot : ¬ RootHeldByOther st.T B) (σ' : Block V → Protocol.ChainState V) (c : Stamp) :
    StoreOk { st with
      σ := σ'
      T := st.T ∪ {B}
      timestamp_block := Function.update st.timestamp_block B (some c) } := by
  obtain ⟨⟨h1, h2, h3⟩, hr, hp, hF⟩ := h
  refine ⟨⟨?_, h2, h3⟩, ?_, ?_, Finset.mem_union_left _ hF⟩
  · intro X hX
    apply update_ne_none
    intro hne
    rcases Finset.mem_union.mp hX with hX | hX
    · exact h1 X hX
    · exact absurd (Finset.mem_singleton.mp hX) hne
  · have key : ∀ X ∈ st.T, X.root = B.root → X = B := by
      intro X hX hXr
      by_contra hne
      exact hroot ⟨X, hX, hne, hXr⟩
    intro X hX Y hY hXY
    rcases Finset.mem_union.mp hX with hX | hX <;> rcases Finset.mem_union.mp hY with hY | hY
    · exact hr X hX Y hY hXY
    · rw [Finset.mem_singleton.mp hY] at hXY ⊢
      exact key X hX hXY
    · rw [Finset.mem_singleton.mp hX] at hXY ⊢
      exact (key Y hY hXY.symm).symm
    · rw [Finset.mem_singleton.mp hX, Finset.mem_singleton.mp hY]
  · intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact Finset.mem_union_left _ (hp X hX)
    · rw [Finset.mem_singleton.mp hX]
      exact Finset.mem_union_left _ hpar

/-- A block the store admits (`Protocol.block_admissible`) has its parent in the tree. -/
theorem parent_mem_of_admissible (C : Config) (P : Provisional V) (st : Store V) (B : Block V)
    (h : Protocol.block_admissible C P st B = true) : B.parent ∈ st.T := by
  unfold Protocol.block_admissible at h
  simp only [Id.run] at h
  by_contra hp
  simp [hp] at h

/-- `Handlers.blockCore` keeps `StoreOk` when the tree holds `B`'s parent and no other block of the
    tree has `B`'s root. -/
theorem blockCore (C : Config) (P : Provisional V) {st : Store V} (h : StoreOk st) {B : Block V}
    (hpar : B.parent ∈ st.T) (hroot : ¬ RootHeldByOther st.T B) :
    StoreOk (Handlers.blockCore C P st B) := by
  have heq : Handlers.blockCore C P st B = Protocol.update_finality
      (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
        { st with σ := Function.update st.σ B (Protocol.state_transition C P (st.σ B.parent) B),
                  T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) })
      B := by
    simp only [Handlers.blockCore, Id.run, List.forIn_pure_yield_eq_foldl]
    rfl
  rw [heq]
  exact update_finality (foldl_checked P _ (insert h hpar hroot _ _)) B

/-- `Handlers.admitBlockCore` keeps `StoreOk` when no other block of the tree has `B`'s root. -/
theorem admitBlockCore (C : Config) (P : Provisional V) {st : Store V} (h : StoreOk st)
    {B : Block V} (hroot : ¬ RootHeldByOther st.T B) :
    StoreOk (Handlers.admitBlockCore C P st B) := by
  unfold Handlers.admitBlockCore
  split_ifs with hadm
  · exact blockCore C P h (parent_mem_of_admissible C P st B hadm) hroot
  · exact h

/-- `Protocol.on_block` keeps `StoreOk` when no other block of the tree has `B`'s root. -/
theorem on_block (C : Config) (P : Provisional V) {st : Store V} (h : StoreOk st) {B : Block V}
    (hroot : ¬ RootHeldByOther st.T B) : StoreOk (Protocol.on_block C P st B) := by
  rw [Handlers.on_block_eq]
  split_ifs
  · exact admit_attestations C (admitBlockCore C P h hroot) _
  · exact h

/-- `Handlers.onBlockUsing` keeps `StoreOk` when no other block of the tree has `B`'s root, whatever
    chain-state builder it is given. -/
theorem onBlockUsing (P : Provisional V) {st : Store V} (h : StoreOk st) {B : Block V}
    (hroot : ¬ RootHeldByOther st.T B)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    StoreOk (Handlers.onBlockUsing P st B buildState) := by
  unfold Handlers.onBlockUsing
  simp only [Id.run]
  split_ifs with h1 h2 h3 h4 <;> first | exact h | skip
  have hpar : B.parent ∈ st.T := by
    by_contra hp
    simp [hp] at h1
  rw [List.forIn_pure_yield_eq_foldl]
  exact update_finality (foldl_checked P _ (insert h hpar hroot _ _)) B

/-! ## Writers of the members that take a store of the type -/

omit [Fintype V] in
/-- A store meeting `StoreOk`, with its chain states, its tree and its block stamps replaced, meets
    `StoreOk` when the result meets `TreeOk`. -/
theorem of_treeOk {st : Store V} (h : StoreOk st) (σ' : Block V → Protocol.ChainState V)
    (T' : Finset (Block V)) (τ' : Block V → Option Stamp)
    (ht : TreeOk { st with σ := σ', T := T', timestamp_block := τ' }) :
    StoreOk { st with σ := σ', T := T', timestamp_block := τ' } :=
  ⟨⟨ht.1, h.1.2.1, h.1.2.2⟩, ht.2.1, ht.2.2.1, ht.2.2.2⟩

/-- `Handlers.admitCarried` keeps `StoreOk` of the store `after`. -/
theorem admitCarried (C : Config) (before : Store V) {after : Store V} (h : StoreOk after)
    (B : Block V) : StoreOk (Handlers.admitCarried C before after B) := by
  unfold Handlers.admitCarried
  split_ifs
  · exact admit_attestations C h _
  · exact h

/-- `Member.receipt_process` keeps `StoreOk`, unless the object is a block whose root another block
    of the tree has (`objectRootHeldByOther`). -/
theorem receipt_process [Inhabited V] (S : DecoupledConsensusModel.Execution.Setup V)
    {st : Store V} (h : StoreOk st) {o : DecoupledConsensusModel.Execution.NamedObject V}
    (ho : ¬ objectRootHeldByOther st.T o) : StoreOk (Member.receipt_process S st o) := by
  cases o with
  | block B => exact on_block _ _ h ho
  | gfVote u => exact on_goldfish_vote_checked _ h _
  | attest a => exact admit_attestation _ h _

end OkStore

end SpecDraftRecord
