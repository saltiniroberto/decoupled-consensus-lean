import Proofs.Claims.Spec2Claims.Claim13beRoute3_75
import Proofs.Claims.Spec2Claims.Claim13beRoute3_74
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf

/-!
# Some validator is not held

Where the adversary holds less than a third of the total weight, some validator is outside its set.
-/

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If three times the adversary's weight at `t` is less than the total weight, some validator is
    not in `Sched.adv t`. -/
theorem exists_not_adv_l76 (S : Setup V) (Sched : Schedule V) {t : Int}
    (hthird : 3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) :
    ∃ v : V, v ∉ Sched.adv t := by
  classical
  by_contra hall
  push Not at hall
  have huniv : Sched.adv t = (Finset.univ : Finset V) := Finset.eq_univ_iff_forall.2 hall
  rw [huniv] at hthird
  have hw : S.E.electorate.weightOf (Finset.univ : Finset V) = S.E.electorate.totalWeight :=
    weightOf_univ S.E.electorate
  rw [hw] at hthird
  omega

end AtRn

end DecoupledConsensusModel.Sts
