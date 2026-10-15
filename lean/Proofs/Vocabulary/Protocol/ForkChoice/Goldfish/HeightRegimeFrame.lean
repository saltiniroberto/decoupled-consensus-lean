module
public import Proofs.Vocabulary.Protocol.ChainState.RecoveryPrefix
public import Proofs.Vocabulary.Protocol.ChainState.SlashableBoundBridge
public import Proofs.Vocabulary.Protocol.Evidence.ProvenanceBridge
public import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
public import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

/-!
# The finality floor

`FinalityFloorAt`, the condition that every honest finalized block over an event prefix is an
ancestor of every run block of height at least `blocked` that descends from `Tprev`, and the bound
it gives on an honest store's `h_max`.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If every honest `h_max` before event `stop` is less than `blocked + 2`, and an honest store
    before event `n ≤ stop` holds a block `Q` of chain-state height `blocked + 1`, then that store's
    `h_max` is `blocked + 1`. -/
theorem localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho)
    {stop : Nat} {blocked : Height}
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {n : Nat} {reader : V} {Q : Block V}
    (hreader : reader ∈ rho.honest) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (rho.stateBefore S n reader).st.T)
    (hQheight : ((rho.stateBefore S n reader).st.σ Q).h = blocked + 1) :
    (rho.stateBefore S n reader).st.h_max = blocked + 1 := by
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n reader hQmem
  have hagree : (rho.stateBefore S n reader).st.core.σ Q =
      Protocol.derive_named S.E S.cfg D := by
    rw [← hDerase]
    exact Proofs.NamedStoreBridge.derivedView_stateBefore S rho n reader D hDmem
  have hQle : blocked + 1 ≤ (rho.stateBefore S n reader).st.h_max := by
    have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore S rho n reader D hDmem
    rw [← hagree, hQheight] at hbound
    exact hbound
  have hfrontierN : honestHMaxBeforeIndex S rho n < blocked + 2 :=
    (honestHMaxBeforeIndex_mono S rho hnstop).trans_lt hfrontier
  have hfrontierNle : honestHMaxBeforeIndex S rho n ≤ blocked + 1 := by
    apply Nat.lt_succ_iff.mp
    simpa only [Nat.add_assoc] using hfrontierN
  have hupper : (rho.stateBefore S n reader).st.h_max ≤ blocked + 1 :=
    (localHMax_le_honestHMaxBeforeIndex S rho n hreader).trans hfrontierNle
  exact Nat.le_antisymm hupper hQle


/-- Every honest finalized block before event `stop` is an ancestor of every run block of height at
    least `blocked` that descends from `Tprev`. -/
def FinalityFloorAt (S : Setup V) (rho : Run V) (blocked : Height) (stop : Nat)
    (Tprev : Block V) : Prop :=
  ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
    ∀ X : NamedBlock V, RunBlock S rho X →
      blocked ≤ (Protocol.derive_named S.E S.cfg X).h →
    Block.Preceq Tprev X.erase → Block.Preceq (rho.stateBefore S n v).st.F X.erase


/-- Every honest finalized block before event `stop` is an ancestor of every run block of height
    `blocked + 1` that descends from `Tprev`. -/
theorem FinalityFloorAt.storeF_preceq_sourceHeightBlock
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat} {Tprev : Block V}
    (h : FinalityFloorAt S rho blocked stop Tprev)
    {n : Nat} {reader : V} (hreader : reader ∈ rho.honest)
    (hnstop : n ≤ stop) {P : NamedBlock V}
    (hPrun : RunBlock S rho P)
    (hPheight : (Protocol.derive_named S.E S.cfg P).h = blocked + 1)
    (hTP : Block.Preceq Tprev P.erase) :
    Block.Preceq (rho.stateBefore S n reader).st.F P.erase :=
  h reader hreader n hnstop P hPrun (hPheight ▸ Nat.le_succ blocked) hTP


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
