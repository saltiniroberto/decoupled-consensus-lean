import Proofs.Vocabulary.Execution.BridgesCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# A held block was processed

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: along a path `W`
of a run, a named block a validator holds among its bodies is the genesis block or was processed by
it at an earlier event.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Execution
open Execution.NamedReceiptCalls
open NamedReceiptCallsBase

/-- For every path `W` of `rho`, every named block `B` among `v`'s bodies in `W i` is the genesis
    block, or is processed by `v`, along `W`, at the time of some event `j < i`. -/
theorem Vocabulary.Proofs.Bridges.processes_block_of_mem_T (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) :
    ∀ (i : Nat) (B : NamedBlock V), B ∈ (W i v).st.bodies →
      B = NamedBlock.genesis ∨
        ∃ (j : Nat) (e : Record.Event V), j < i ∧ rho.events[j]? = some e ∧
          Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.block B) e.time := by
  intro i
  induction i with
  | zero =>
    intro B hB
    exact Or.inl (facts.ndRun.stateBefore_zero_body_eq_genesis S rho v (W 0) (hW 0).1 hB)
  | succ i ih =>
    intro B hB
    by_cases hpre : B ∈ (W i v).st.bodies
    · rcases ih B hpre with h | ⟨j, e, hj, hje, hproc⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, e, Nat.lt_succ_of_lt hj, hje, hproc⟩
    · refine Or.inr ?_
      obtain ⟨t, hacc⟩ := Restated.Vocabulary.Proofs.NamedReceiptCalls.new_block_accepts facts S rho i v B
        W hW hpre hB
      obtain ⟨⟨hidx, e, he, -, -⟩, -, -⟩ := hacc
      refine ⟨i, e, Nat.lt_succ_self i, he, ?_⟩
      rcases hidx with ⟨t', ht', hmem⟩ | ⟨t', ht'⟩
      · have heeq : e = Record.Event.tick v t' := Option.some.inj (he.symm.trans ht')
        subst heeq
        exact Or.inl ⟨i, ht', hmem⟩
      · have heeq : e = Record.Event.deliver v (.block B) t' :=
          Option.some.inj (he.symm.trans ht')
        subst heeq
        exact Or.inr ⟨i, ht'⟩

end

end DecoupledConsensusModel.Sts.Restated
