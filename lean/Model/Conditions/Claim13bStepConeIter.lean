import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepConeIter

/-!
# Honest heads that descend from a block

The condition `HeadsBelow` that every honest head of a slot descends from a block, and the
conditions `HeadsResolve` and `TreeIdealizes` on a voter's tree, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every member of `HonSlot` for slot `s` and every tick step at slot `s`'s vote time, every
    head that validator's vote duty can select there is a descendant of `B`. -/
def HeadsBelow (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ (v : V) (m : Nat), v ∈ Restated.HonSlot M S Sched s →
    Restated.tickStepAt M x m (M.vote_time S.E s) →
    ∀ G : Block V, Restated.gfHeadFrom M S (x[m][v].st) s ⇢ G → Block.Preceq B G

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every honest active member of slot `s`'s committee and every outcome `G` of that member's
    slot-`s` head, the block `G` names resolves in `v`'s tree at step `mr`, is of a slot at most
    `s`, and carries a block stamp strictly before slot `s`'s support cutoff. -/
def HeadsResolve (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (m mr : Nat) (s : Slot) : Prop :=
  ∀ v' ∈ Restated.HonSlot M S Sched s, ∀ G : Block V, Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G →
    ∃ X : Block V, X.root = G.root ∧ X.slot ≤ s ∧
      Block.find? (x[mr][v].st).st.core.T X.root = some X ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block X = some σ ∧
        σ < ((M.support_cutoff S.E s : Int) : Stamp)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A block of `v`'s tree at step `mr` that resolves to itself, and whose root is the root of a
    named block in the sent log, is a descendant of `B` whenever that named block's erasure is. -/
def TreeIdealizes (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (mr : Nat) (B : Block V) : Prop :=
  ∀ (X : Block V) (H : NamedBlock V),
    Block.find? (x[mr][v].st).st.core.T X.root = some X →
    Restated.blockInLog M S Sched x H → X.root = H.root → Block.Preceq B H.erase → Block.Preceq B X

end

end DecoupledConsensusModel.Sts.Restated
