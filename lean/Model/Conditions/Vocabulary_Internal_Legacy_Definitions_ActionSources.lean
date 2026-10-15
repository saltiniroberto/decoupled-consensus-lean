import Proofs.Vocabulary.Internal.Legacy.Definitions.ActionSources
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Record.Wiring

/-!
# Action-time reads and sources

The node states, attestations, SG blocks and FG sources read at round `r`'s action time, as sets
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- The set of `v`'s node states after the confirmation duty at round `r`'s action time. -/
def Vocabulary.Proofs.HealingSurface.actionReadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR M.N :=
  Restated.Vocabulary.Execution.NamedActionReads.actionReadAt M S rho v r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- The set of `v`'s prepared action node states at round `r`, which is `actionReadAt M S rho v r`. -/
def Vocabulary.Proofs.HealingSurface.actionStoreAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR M.N :=
  Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- The set of attestations the attestation duty can return from some node state in
    `actionReadAt M S rho v r`. -/
def Vocabulary.Proofs.HealingSurface.actionAttestationAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR (NamedAttestation V) :=
  { a | ∃ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∃ (ns : M.NS) (rec : M.NR), M.duties_attest_with (M.gradeContract n.cache)
      S.E S.hc (S.node v) n.st n.record ⇢ (ns, rec, a) }

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- The set of blocks the SG vote selection can return from some node state in
    `actionReadAt M S rho v r`, given an outcome of the grade-2 block read at the round of its
    store's slot. -/
def Vocabulary.Proofs.HealingSurface.actionSGBlockAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR (Block V) :=
  { B | ∃ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    let gc := M.gradeContract n.cache
    let st := (M.toHealing n.st.core)
    let k := (M.round_of S.hc st.s)
    ∃ g, M.grade2_block_with gc S.E S.hc st k ⇢ g ∧ M.get_sg_vote_with gc S.E S.hc st k g ⇢ B }

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- The outcomes of the FG source read on `n`'s healing store at the round of its slot, under `n`'s
    grade contract, for every outcome of the grade-2 block read there. -/
def Vocabulary.Proofs.HealingSurface.actionFGSource (M : Record.Model V) (S : Setup V) (n : M.N) :
    DC.NDRE (Option (Block V)) :=
  let gc := M.gradeContract n.cache
  let st := (M.toHealing n.st.core)
  let r := (M.round_of S.hc st.s)
  do
    let g ← M.grade2_block_with gc S.E S.hc st r
    M.fg_source_with gc S.E S.hc st r g

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- For every outcome `o` of `actionFGSource M S n`, the block `(n.st.core.σ Cfg).T_h` when `o` is
    `some Cfg`, and none when `o` is none. -/
def Vocabulary.Proofs.HealingSurface.fgConfirmationWitness (M : Record.Model V) (S : Setup V) (n : M.N) :
    DC.NDRE (Option (Block V)) :=
  (fun o : Option (Block V) => o.map (fun Cfg => (n.st.core.σ Cfg).T_h)) <$>
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.actionReadAt` is
    the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.actionReadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.actionReadAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Proofs.HealingSurface.actionReadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.actionReadAt (V := V) S rho v r} :=
  Vocabulary.Execution.NamedActionReads.actionReadAt_vocabulary_eq S rho v r

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt` is
    the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.actionStoreAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.actionStoreAt (V := V) S rho v r} :=
  Vocabulary.Proofs.HealingSurface.actionReadAt_vocabulary_eq S rho v r

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt` is the singleton of
    `DecoupledConsensusModel.Proofs.HealingSurface.actionAttestationAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.actionAttestationAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.actionAttestationAt (V := V) S rho v r} :=
  by
  rw [Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt,
    Vocabulary.Proofs.HealingSurface.actionReadAt_vocabulary_eq]
  ext a
  constructor
  · rintro ⟨n, hn, ns, rec, h⟩
    have hn' : n = _ := hn
    subst hn'
    have h' := (Record.returns_pure _ _).1 h
    exact congrArg (fun p => p.2.2) h'
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨_, rfl, _, _, (Record.returns_pure _ _).2 rfl⟩

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt`
    is the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.actionSGBlockAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.actionSGBlockAt (V := V) S rho v r} :=
  by
  rw [Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt,
    Vocabulary.Proofs.HealingSurface.actionReadAt_vocabulary_eq]
  ext B
  constructor
  · rintro ⟨n, hn, g, hg, hB⟩
    have hn' : n = _ := hn
    subst hn'
    have hg' := (Record.returns_pure _ _).1 hg
    subst hg'
    exact (Record.returns_pure _ _).1 hB
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨_, rfl, _, (Record.returns_pure _ _).2 rfl, (Record.returns_pure _ _).2 rfl⟩

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.actionFGSource`
    has the single outcome `DecoupledConsensusModel.Proofs.HealingSurface.actionFGSource`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.actionFGSource_vocabulary_eq (S : Setup V) (n : NamedNodeState V) :
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource (V := V) Record.Model.vocabulary S n =
      pure (_root_.DecoupledConsensusModel.Proofs.HealingSurface.actionFGSource (V := V) S n) := by
  show (pure _ >>= fun g => pure _ : DC.NDRE (Option (Block V))) = _
  rw [pure_bind]
  rfl

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness` has the single outcome
    `DecoupledConsensusModel.Proofs.HealingSurface.fgConfirmationWitness`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.fgConfirmationWitness_vocabulary_eq (S : Setup V) (n : NamedNodeState V) :
    Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness (V := V) Record.Model.vocabulary S n =
      pure (_root_.DecoupledConsensusModel.Proofs.HealingSurface.fgConfirmationWitness (V := V) S n) := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness,
    Vocabulary.Proofs.HealingSurface.actionFGSource_vocabulary_eq, map_pure]
  rfl

end

end DecoupledConsensusModel.Sts.Restated
