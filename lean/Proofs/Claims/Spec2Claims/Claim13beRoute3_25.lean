import Proofs.Claims.Spec2Claims.Claim13beRoute3_24
import Proofs.Claims.Spec2Claims.Claim13beRoute3_22
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_gf_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time

/-!
# The state a tick reads

In a run sorted by key in which a tick event sits at one index only, the state a tick reads is the
validator's state strictly before the tick's instant. The file also defines `priv%`, a term for a
private declaration of an imported module.
-/

set_option autoImplicit false

open Lean Elab Term Meta in
/-- `priv% M N` is the private declaration `N` of the imported module `M`, the constant
    `_private.M.0.N`. -/
elab "priv% " m:ident n:ident : term => do
  let nm := (Name.mkNum (`_private ++ m.getId) 0) ++ n.getId
  mkConstWithFreshMVarLevels nm

namespace DecoupledConsensusModel.Proofs.NamedRuntime
open Execution
open NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

/-- In a run sorted by key in which a tick event sits at one index only, the state a tick of `v` at
    `t` reads is `v`'s state strictly before instant `t`. -/
theorem tick_prefix_eq_strict_of_fields (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (huniq : Sts.TickIndexUnique rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    stateBefore S rho i v = stateBeforeTime S rho t v := by
  have hfilter := (priv% Proofs.Vocabulary.Execution.Runtime
    DecoupledConsensusModel.Proofs.NamedRuntime.filter_eq_take_sorted) rho hsorted _
    ((priv% Proofs.Vocabulary.Execution.Runtime
      DecoupledConsensusModel.Proofs.NamedRuntime.downward_lt) t)
  have hni : (rho.events.filter (fun e => decide (e.time < t))).length ≤ i := by
    by_contra hcon
    have hlt : i < (rho.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hcon
    have hmem : NamedEvent.tick v t ∈ rho.events.filter (fun e => decide (e.time < t)) := by
      rw [hfilter]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, NamedEvent.time] at hp
    exact lt_irrefl _ hp
  have hread : stateBeforeTime S rho t =
      stateBefore S rho (rho.events.filter (fun e => decide (e.time < t))).length := by
    exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init) hfilter
  rw [hread]
  refine stateBefore_eq_of_ne S rho v i hni ?_
  intro j e hj hji hget
  have hlow : t ≤ e.time := by
    have hf := (priv% Proofs.Vocabulary.Execution.Runtime
      DecoupledConsensusModel.Proofs.NamedRuntime.filter_false_of_index_ge_sorted) rho hsorted _
      ((priv% Proofs.Vocabulary.Execution.Runtime
        DecoupledConsensusModel.Proofs.NamedRuntime.downward_lt) t) hj hget
    simpa using hf
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hkey : NamedEvent.key e ≤ NamedEvent.key (NamedEvent.tick v t) := by
    have hp := (List.pairwise_iff_getElem.mp hsorted) j i hjl hil hji
    rw [hje, hie] at hp
    exact hp
  have hteq : NamedEvent.time e = t :=
    le_antisymm (Proofs.Bridges.time_le_of_key_le hkey) hlow
  intro hnode
  have heq : e = NamedEvent.tick v t := by
    cases e with
    | tick u t' =>
      simp only [NamedEvent.node] at hnode
      simp only [NamedEvent.time] at hteq
      rw [hnode, hteq]
    | deliver u o t' =>
      exfalso
      simp only [NamedEvent.time] at hteq
      subst hteq
      simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase, Prod.Lex.toLex_le_toLex] at hkey
  have hev : rho.events[j] = rho.events[i] := by rw [hje, hie, heq]
  have hij : j = i := huniq (hje.trans heq) hev
  omega

end DecoupledConsensusModel.Proofs.NamedRuntime

namespace DecoupledConsensusModel.Proofs.NamedCacheProvenance
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedCacheProvenance

namespace DecoupledConsensusModel
namespace Protocol
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end Protocol
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end Protocol
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end Optimistic
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal
open Execution
open Internal.NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.NamedRawRelay
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedRawRelay

namespace DecoupledConsensusModel.Proofs.NamedSGArrival
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedSGArrival

namespace DecoupledConsensusModel.Proofs.NamedRelayGuards
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedRelayGuards

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end Optimistic
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas
variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end Optimistic
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Protocol
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end Protocol
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel
