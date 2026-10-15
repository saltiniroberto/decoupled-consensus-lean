module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Mathlib.Data.Rat.Floor
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Vocabulary.Objects.ActionRound

@[expose] public section


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


/-! ## The finalized block is an ancestor of the FG root -/

/-- In an admissible run, the finalized block of `w`'s store before time `t` is an ancestor of that
    store's FG root `get_fg_root`. -/
theorem finalizedRoot_preceq_fgRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {w : V} {t : Time} :
    Block.Preceq (rho.storeBeforeTime S w t).F
      (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG) := by
  have hFJ : Block.Preceq (rho.storeBeforeTime S w t).F
      (rho.storeBeforeTime S w t).J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t w
  simp only [Protocol.get_fg_root, Protocol.Store.toHealing]
  split
  · exact hFJ
  · exact Block.preceq_self _


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
