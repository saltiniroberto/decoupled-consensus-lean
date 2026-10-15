module
public import Proofs.Vocabulary.Protocol.ValidatorClient.Bridge
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import Proofs.Vocabulary.Protocol.Handlers.JustificationBound
public import Proofs.Vocabulary.Protocol.Evidence.ProvenanceBridge
public import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


/-!
# Ancestry helpers for named blocks

Helpers on the ancestry of named blocks and on the attestations of a named block's chain.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
private theorem preceq_cases {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    A = B ∨ NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
      left
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using h
  | node p s root gf support rows proposer =>
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent, Bool.or_eq_true,
        decide_eq_true_eq] using h

omit [Fintype V] in
private theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      have hB : B = .genesis := by simpa [NamedBlock.Preceq, NamedBlock.preceq] using hBC
      simpa only [← hB] using hAB
  | node p s root gf support rows proposer ih =>
      rcases preceq_cases hBC with rfl | hparent
      · exact hAB
      · change (decide (A = .node p s root gf support rows proposer) ||
          NamedBlock.preceq A p) = true
        simp only [Bool.or_eq_true]
        exact Or.inr (ih hparent)

omit [Fintype V] in
private theorem mem_named_chain_attestations_own {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) : a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
