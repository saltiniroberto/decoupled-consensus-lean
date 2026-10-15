import Proofs.Vocabulary.Internal.Definitions.NamedProposalPivot
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Record.Wiring

/-!
# The Goldfish walks of a proposer and a voter

The source and target trees, scores and eligibility tests of the Goldfish walks of a slot's proposer
and of a voter, and the transfer of the walk between them, stated over a model `M : Record.Model V`,
and their counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The set of filtered block trees of the store of `n`, for every read `n` that slot `s`'s proposer
    hands its proposal duty. -/
def Vocabulary.Proofs.HealingSurface.namedWalkSourceTree (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    DC.NDR (Finset (Block V)) :=
  (fun n : M.N => M.get_filtered_block_tree (M.toHealing n.st.core).toFG) ''
    Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The score functions `sc` such that, for some proposal duty read `n` of slot `s`'s proposer and
    some outcome `psv` of its support view, `sc B` is an outcome of the Goldfish score of `B` in
    `n`'s store over the proposer's view and `psv`, for every block `B`. -/
def Vocabulary.Proofs.HealingSurface.namedWalkSourceScore (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    DC.NDR (Block V → Nat) :=
  {sc | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s,
    ∃ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv ∧
      ∀ B : Block V, M.goldfish_score S.E n.st.core.T
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ sc B}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The eligibility functions `el` such that, for some proposal duty read `n` of slot `s`'s proposer
    and some outcome `psv` of its support view, `el B` is an outcome of the Goldfish eligibility
    test of `B` in `n`'s store over the proposer's view and `psv`, for every block `B`. -/
def Vocabulary.Proofs.HealingSurface.namedWalkSourceEligible (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    DC.NDR (Block V → Bool) :=
  {el | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s,
    ∃ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv ∧
      ∀ B : Block V, M.goldfish_eligible S.E n.st.core.σ n.st.core.h_max n.st.core.T n.st.core.s
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ el B}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The trees `T` without the erasure of `P`, for every vote duty read `m` of `v` at slot `s` and
    every outcome `T` of the voter's filtered block tree of `m`'s store at its slot. -/
def Vocabulary.Proofs.HealingSurface.namedWalkTargetTree (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) (v : V) (P : NamedBlock V) :
    DC.NDR (Finset (Block V)) :=
  {T' | ∃ m ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T ∧
      T' = T.erase P.erase}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The score functions `sc` such that, for some vote duty read `m` of `v` at slot `s` and some
    outcomes `vv` and `vsv` of the voter's view and support view in `m`'s store, `sc B` is an
    outcome of the Goldfish score of `B` in `m`'s store over `vv` and `vsv`, for every block `B`. -/
def Vocabulary.Proofs.HealingSurface.namedWalkTargetScore (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) (v : V) :
    DC.NDR (Block V → Nat) :=
  {sc | ∃ m ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∃ vv vsv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv ∧
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv ∧
      ∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ sc B}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The eligibility functions `el` such that, for some vote duty read `m` of `v` at slot `s` and
    some outcomes `vv` and `vsv` of the voter's view and support view in `m`'s store, `el B` is an
    outcome of the Goldfish eligibility test of `B` in `m`'s store over `vv` and `vsv`, for every
    block `B`. -/
def Vocabulary.Proofs.HealingSurface.namedWalkTargetEligible (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) (v : V) :
    DC.NDR (Block V → Bool) :=
  {el | ∃ m ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    ∃ vv vsv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv ∧
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv ∧
      ∀ B : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) B ⇢ el B}

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The Goldfish walk from `E` toward the proposal's parent agrees between the proposer read `n` and
    the voter read `m`: each block the proposer's walk steps to is in the voter's tree without `P`
    and passes the voter's eligibility test (`persist`), and each child the voter's test can pass
    along that path is in the proposer's tree and passes the proposer's test (`reflect`). -/
structure Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) (E : Block V)
    (v : V) (P : NamedBlock V) (n m : M.N) : Prop where
  persist :
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache)
        S.E S.hc (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
    ∀ srcScore : Block V → Nat,
      (∀ B : Block V, M.goldfish_score S.E n.st.core.T
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ srcScore B) →
    ∀ srcEligible : Block V → Bool,
      (∀ B : Block V, M.goldfish_eligible S.E n.st.core.σ n.st.core.h_max n.st.core.T n.st.core.s
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ srcEligible B) →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
    ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
    let parent := input.parent
    let srcTree := M.get_filtered_block_tree (M.toHealing n.st.core).toFG
    ∀ X C : Block V,
    Block.Preceq E X →
    Block.Preceq X parent →
    X ≠ parent →
    M.ghost_step srcTree srcScore srcEligible X ⇢ some C →
    Block.Preceq C parent →
    C ∈ T.erase P.erase ∧
      ∀ b : Bool, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) C ⇢ b → b = true
  reflect :
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache)
        S.E S.hc (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
    ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
    let parent := input.parent
    let srcTree := M.get_filtered_block_tree (M.toHealing n.st.core).toFG
    ∀ X C : Block V,
    Block.Preceq E X →
    Block.Preceq X parent →
    C ∈ T.erase P.erase →
    C.parent? = some X →
    M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
      vv vsv (m.st.core.s - 1) C ⇢ true →
    C ∈ srcTree ∧
      ∀ b : Bool, M.goldfish_eligible S.E n.st.core.σ n.st.core.h_max n.st.core.T n.st.core.s
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) C ⇢ b → b = true

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedWalkSourceTree` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.namedWalkSourceTree`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedWalkSourceTree_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.namedWalkSourceTree (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.namedWalkSourceTree (V := V) S rho s} := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.namedWalkSourceTree,
    Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead_vocabulary_eq]
  exact Set.image_singleton

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedWalkSourceScore` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.namedWalkSourceScore`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedWalkSourceScore_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.namedWalkSourceScore (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.namedWalkSourceScore (V := V) S rho s} := by
  ext sc
  rw [Restated.Vocabulary.Proofs.HealingSurface.namedWalkSourceScore,
    Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, psv, hpsv, hsc⟩
    obtain rfl := Set.mem_singleton_iff.mp hn
    obtain rfl := (Record.returns_pure _ _).1 hpsv
    exact Set.mem_singleton_iff.mpr (funext fun B => (Record.returns_pure _ _).1 (hsc B))
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨_, Set.mem_singleton _, _, (Record.returns_pure _ _).2 rfl,
      fun B => (Record.returns_pure _ _).2 rfl⟩

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedWalkSourceEligible` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.namedWalkSourceEligible`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedWalkSourceEligible_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.namedWalkSourceEligible (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.namedWalkSourceEligible (V := V) S rho s} := by
  ext el
  rw [Restated.Vocabulary.Proofs.HealingSurface.namedWalkSourceEligible,
    Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, psv, hpsv, hel⟩
    obtain rfl := Set.mem_singleton_iff.mp hn
    obtain rfl := (Record.returns_pure _ _).1 hpsv
    exact Set.mem_singleton_iff.mpr (funext fun B => (Record.returns_pure _ _).1 (hel B))
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨_, Set.mem_singleton _, _, (Record.returns_pure _ _).2 rfl,
      fun B => (Record.returns_pure _ _).2 rfl⟩

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedWalkTargetTree` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.namedWalkTargetTree`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedWalkTargetTree_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (v : V) (P : NamedBlock V) :
    Restated.Vocabulary.Proofs.HealingSurface.namedWalkTargetTree (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s v P =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.namedWalkTargetTree (V := V) S rho s v P} := by
  ext T'
  rw [Restated.Vocabulary.Proofs.HealingSurface.namedWalkTargetTree,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨m, hm, T, hT, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp hm
    obtain rfl := (Record.returns_pure _ _).1 hT
    exact Set.mem_singleton _
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨_, Set.mem_singleton _, _, (Record.returns_pure _ _).2 rfl, rfl⟩

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedWalkTargetScore` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.namedWalkTargetScore`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedWalkTargetScore_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (v : V) :
    Restated.Vocabulary.Proofs.HealingSurface.namedWalkTargetScore (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s v =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.namedWalkTargetScore (V := V) S rho s v} := by
  ext sc
  rw [Restated.Vocabulary.Proofs.HealingSurface.namedWalkTargetScore,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨m, hm, vv, vsv, hvv, hvsv, hsc⟩
    obtain rfl := Set.mem_singleton_iff.mp hm
    obtain rfl := (Record.returns_pure _ _).1 hvv
    obtain rfl := (Record.returns_pure _ _).1 hvsv
    exact Set.mem_singleton_iff.mpr (funext fun B => (Record.returns_pure _ _).1 (hsc B))
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨_, Set.mem_singleton _, _, _, (Record.returns_pure _ _).2 rfl,
      (Record.returns_pure _ _).2 rfl, fun B => (Record.returns_pure _ _).2 rfl⟩

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `namedWalkTargetEligible` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.HealingSurface.namedWalkTargetEligible`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.namedWalkTargetEligible_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (v : V) :
    Restated.Vocabulary.Proofs.HealingSurface.namedWalkTargetEligible (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s v =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.namedWalkTargetEligible (V := V) S rho s v} := by
  ext el
  rw [Restated.Vocabulary.Proofs.HealingSurface.namedWalkTargetEligible,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  constructor
  · rintro ⟨m, hm, vv, vsv, hvv, hvsv, hel⟩
    obtain rfl := Set.mem_singleton_iff.mp hm
    obtain rfl := (Record.returns_pure _ _).1 hvv
    obtain rfl := (Record.returns_pure _ _).1 hvsv
    exact Set.mem_singleton_iff.mpr (funext fun B => (Record.returns_pure _ _).1 (hel B))
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨_, Set.mem_singleton _, _, _, (Record.returns_pure _ _).2 rfl,
      (Record.returns_pure _ _).2 rfl, fun B => (Record.returns_pure _ _).2 rfl⟩

/-- At `Record.Model.vocabulary`,
    `DecoupledConsensusModel.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer` holds exactly
    when the restated `NamedProposalPivotSuffixTransfer` holds at the one proposer read and the one
    read of `v`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) (E : Block V) (v : V) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer (V := V) S rho s E v P ↔
      Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s E v P
        (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.proposalDutyRead S rho s)
        (_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead S rho v s) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro input hin psv hpsv sc hsc el hel T hT vv hvv vsv hvsv _ _ X C h1 h2 h3 h4 h5
      obtain rfl := (Record.returns_pure _ _).1 hin
      obtain rfl := (Record.returns_pure _ _).1 hpsv
      obtain rfl := (Record.returns_pure _ _).1 hT
      obtain rfl := (Record.returns_pure _ _).1 hvv
      obtain rfl := (Record.returns_pure _ _).1 hvsv
      obtain rfl : sc = _ := funext fun B => (Record.returns_pure _ _).1 (hsc B)
      obtain rfl : el = _ := funext fun B => (Record.returns_pure _ _).1 (hel B)
      obtain ⟨hmem, helig⟩ := h.persist X C h1 h2 h3 ((Record.returns_pure _ _).1 h4).symm h5
      exact ⟨hmem, fun b hb => ((Record.returns_pure _ _).1 hb).trans helig⟩
    · intro input hin psv hpsv T hT vv hvv vsv hvsv _ _ X C h1 h2 h3 h4 h5
      obtain rfl := (Record.returns_pure _ _).1 hin
      obtain rfl := (Record.returns_pure _ _).1 hpsv
      obtain rfl := (Record.returns_pure _ _).1 hT
      obtain rfl := (Record.returns_pure _ _).1 hvv
      obtain rfl := (Record.returns_pure _ _).1 hvsv
      obtain ⟨hmem, helig⟩ := h.reflect X C h1 h2 h3 h4 ((Record.returns_pure _ _).1 h5).symm
      exact ⟨hmem, fun b hb => ((Record.returns_pure _ _).1 hb).trans helig⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro X C h1 h2 h3 h4 h5
      obtain ⟨hmem, helig⟩ := h.persist _ ((Record.returns_pure _ _).2 rfl)
        _ ((Record.returns_pure _ _).2 rfl) _ (fun B => (Record.returns_pure _ _).2 rfl)
        _ (fun B => (Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
        _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
        X C h1 h2 h3 ((Record.returns_pure _ _).2 h4.symm) h5
      exact ⟨hmem, helig _ ((Record.returns_pure _ _).2 rfl)⟩
    · intro X C h1 h2 h3 h4 h5
      obtain ⟨hmem, helig⟩ := h.reflect _ ((Record.returns_pure _ _).2 rfl)
        _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
        _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
        X C h1 h2 h3 h4 ((Record.returns_pure _ _).2 h5.symm)
      exact ⟨hmem, helig _ ((Record.returns_pure _ _).2 rfl)⟩

end

end DecoupledConsensusModel.Sts.Restated
