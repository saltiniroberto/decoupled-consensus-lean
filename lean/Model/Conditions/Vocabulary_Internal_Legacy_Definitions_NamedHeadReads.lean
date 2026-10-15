import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedHeadReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Record.Wiring

/-!
# Voter and action heads

The heads a validator can compute at its Goldfish vote duty and at a round's action, as sets of
blocks over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Execution Proofs.HealingSurface NamedRecoveryRead

/-- The set of heads `v` can compute at the Goldfish vote time of slot `k` from its vote duty read,
    with the voter views of that read. -/
def Vocabulary.Internal.voterHeadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (k : Slot) : DC.NDR (Block V) :=
  { B | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v k,
    let st := n.st.core
    (do
      let T ← M.voter_filtered_block_tree S.E st st.s
      let L ← M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
      let L' ← M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing st)
        T L L' (st.s - 1) : DC.NDRE (Block V)) ⇢ B }

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Execution Proofs.HealingSurface NamedRecoveryRead

/-- The set of heads `v` can compute at round `r`'s action time from its action duty read, over the
    pool of its store's slot and the part of that pool marked resolved. -/
def Vocabulary.Internal.actionHeadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) : DC.NDR (Block V) :=
  { B | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.actionDutyRead M S rho v r,
    let st := n.st.core
    (do
      let res ← (ExceptT.lift {res : GoldfishVote V → Bool | ∀ u, M.resolved st.T u ⇢ res u} :
        DC.NDRE (GoldfishVote V → Bool))
      M.get_head_with (M.gradeContract n.cache) S.E S.hc (M.toHealing st)
        ((M.store_pool st st.s)) (((M.store_pool st st.s)).filter (fun u => res u = true)) st.s :
      DC.NDRE (Block V)) ⇢ B }

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Execution Proofs.HealingSurface NamedRecoveryRead

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.voterHeadAt` is the singleton
    of `DecoupledConsensusModel.Internal.voterHeadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.voterHeadAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (k : Slot) :
    Restated.Vocabulary.Internal.voterHeadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v k =
      {_root_.DecoupledConsensusModel.Internal.voterHeadAt (V := V) S rho v k} := by
  rw [Restated.Vocabulary.Internal.voterHeadAt,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  ext B
  constructor
  · rintro ⟨n, hn, h⟩
    have hn' : n = _ := hn
    subst hn'
    simp only [Record.Model.vocabulary, pure_bind] at h
    exact (Record.returns_pure _ _).1 h
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [Record.Model.vocabulary, pure_bind]
    exact (Record.returns_pure _ _).2 rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.actionHeadAt` is the singleton
    of `DecoupledConsensusModel.Internal.actionHeadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.actionHeadAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Internal.actionHeadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Internal.actionHeadAt (V := V) S rho v r} := by
  rw [Restated.Vocabulary.Internal.actionHeadAt,
    Vocabulary.Internal.NamedRecoveryRead.actionDutyRead_vocabulary_eq]
  have hres : ∀ T : Finset (Block V),
      {res : GoldfishVote V → Bool | ∀ u, (Record.Model.vocabulary (V := V)).resolved T u ⇢ res u} =
        {fun u => _root_.DecoupledConsensusModel.Protocol.resolved T u} := by
    intro T
    ext res
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      funext u
      exact (Record.returns_pure _ _).1 (h u)
    · intro h u
      subst h
      exact (Record.returns_pure _ _).2 rfl
  ext B
  constructor
  · rintro ⟨n, hn, h⟩
    have hn' : n = _ := hn
    subst hn'
    simp only [hres, ← Set.pure_def, ExceptT.lift_pure, pure_bind] at h
    exact (Record.returns_pure _ _).1 h
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [hres, ← Set.pure_def, ExceptT.lift_pure, pure_bind]
    exact (Record.returns_pure _ _).2 rfl

end

end DecoupledConsensusModel.Sts.Restated
