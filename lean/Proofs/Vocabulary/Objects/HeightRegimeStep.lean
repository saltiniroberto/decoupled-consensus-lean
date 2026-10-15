module
public import Proofs.Vocabulary.Protocol.Grades.RecoveryFGSelectorPrefixSeed
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
public import Proofs.Vocabulary.Protocol.ChainState.FGRootWitness
public import Proofs.Vocabulary.Protocol.Grades.Q31_actionSGBlock_tiers
public import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import Proofs.Vocabulary.Protocol.Grades.RecoveryGenuineClearNextVote
public import Proofs.Vocabulary.Protocol.Duties.Inputs.FirstProgressFGWitness
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# A named block whose erasure is genesis

A helper: a named block whose erasure is genesis is the named genesis.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem namedGenesis_of_erase_genesis {B : NamedBlock V}
    (h : B.erase = Block.genesis) : B = NamedBlock.genesis := by
  cases B with
  | genesis => rfl
  | node parent s root votes support rows proposer =>
      simp only [NamedBlock.erase] at h
      exact absurd h (by simp)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
