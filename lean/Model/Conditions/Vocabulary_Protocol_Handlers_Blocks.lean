import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Record.Wiring

/-!
# Block tree and block stamps

The invariants of a store's block tree and block timestamps, what carries from one store to a later
one, and admission of a block before a time, stated over a model `M : Record.Model V`, and their
agreement with the definitions of the same name at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The invariant of the block tree `st.T` and its timestamp map: exactly the tree members have a
    block stamp, and every stamp is no later than the store clock. -/
structure Vocabulary.Protocol.BlockStamps (M : Record.Model V) (st : M.S) : Prop where
  /-- Every tree member has a block stamp. -/
  stamped : ∀ B : Block V, B ∈ st.T → (st.timestamp_block B).isSome = true
  /-- Every block stamp belongs to a tree member. -/
  stored : ∀ B : Block V, (st.timestamp_block B).isSome = true → B ∈ st.T
  /-- Every block stamp is at or before the store clock. -/
  bounded : ∀ (B : Block V) (c : Stamp), st.timestamp_block B = some c →
    c ≤ (st.t : Stamp)

end

section
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- What carries from the block store `st` to a later one `st'`: tree members and written block
    stamps. -/
structure Vocabulary.Protocol.BlockCarry (M : Record.Model V) (st st' : M.S) : Prop where
  /-- The tree only grows. -/
  mem : ∀ B : Block V, B ∈ st.T → B ∈ st'.T
  /-- A written block stamp is never rewritten. -/
  stamp : ∀ (B : Block V) (c : Stamp), st.timestamp_block B = some c →
    st'.timestamp_block B = some c

end

section
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- One transition from `st` to `st'` that, from `BlockStamps` at `st`, carries old blocks and
    stamps and preserves `BlockStamps`. -/
def Vocabulary.Protocol.BlockStep (M : Record.Model V) (st st' : M.S) : Prop :=
  Restated.Vocabulary.Protocol.BlockStamps M st → Restated.Vocabulary.Protocol.BlockCarry M st st' ∧ Restated.Vocabulary.Protocol.BlockStamps M st'

end

section
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- Some named block `C` whose erasure is `B` is accepted by `v` at some event of `ρ`, read along
    the path `W`, at a time before `Γ`. -/
def Vocabulary.Protocol.AdmittedBefore (M : Record.Model V) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (v : V) (B : Block V)
    (Γ : Time) : Prop :=
  ∃ C : NamedBlock V, C.erase = B ∧
    ∃ (i : Nat) (t : Time), Restated.Vocabulary.Execution.NamedRun.acceptsAt M S ρ W i v (Object.block C) t ∧ t < Γ

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- `DecoupledConsensusModel.Protocol.BlockStamps` holds exactly when its form over the record holds
    at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.BlockStamps_vocabulary_eq (st : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.BlockStamps (V := V) st ↔ Restated.Vocabulary.Protocol.BlockStamps (V := V) Record.Model.vocabulary st :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary] at *) <;> assumption

/-- `DecoupledConsensusModel.Protocol.BlockCarry` holds exactly when its form over the record holds
    at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.BlockCarry_vocabulary_eq (st st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.BlockCarry (V := V) st st' ↔ Restated.Vocabulary.Protocol.BlockCarry (V := V) Record.Model.vocabulary st st' :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary] at *) <;> assumption

/-- `DecoupledConsensusModel.Protocol.BlockStep` holds exactly when its form over the record holds
    at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.BlockStep_vocabulary_eq (st st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.BlockStep (V := V) st st' ↔ Restated.Vocabulary.Protocol.BlockStep (V := V) Record.Model.vocabulary st st' :=
  imp_congr (Vocabulary.Protocol.BlockStamps_vocabulary_eq st)
    (and_congr (Vocabulary.Protocol.BlockCarry_vocabulary_eq st st')
      (Vocabulary.Protocol.BlockStamps_vocabulary_eq st'))

/-- `DecoupledConsensusModel.Protocol.AdmittedBefore` holds exactly when its form over the record
    holds at `Record.Model.vocabulary`, along the path `fun i => NamedRun.stateBefore S ρ i`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.AdmittedBefore_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (B : Block V) (Γ : Time) :
    _root_.DecoupledConsensusModel.Protocol.AdmittedBefore (V := V) S ρ v B Γ ↔
      Restated.Vocabulary.Protocol.AdmittedBefore (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => Execution.NamedRun.stateBefore S ρ i) v B Γ :=
  exists_congr fun C => and_congr Iff.rfl (exists_congr fun i => exists_congr fun t =>
    and_congr (Vocabulary.Execution.NamedRun.acceptsAt_vocabulary_eq S ρ i v _ t) Iff.rfl)

end

end DecoupledConsensusModel.Sts.Restated
