import Proofs.Vocabulary.Execution.OutageProvenance
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Record.Wiring

/-!
# Where held blocks and rows come from

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, along a path `W`
of a run: a named block a validator holds among its bodies is the genesis block or was accepted by
it at an earlier event, and a row it holds was accepted at an earlier event.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageProvenance
open Execution

/-- For every path `W` of `rho`, if `B` is among `v`'s bodies in `W i`, then `B` is the genesis
    block, or `v` accepts `B` at some event `j < i` of `rho`, at some time `t`, read along `W`. -/
theorem Vocabulary.Proofs.NamedOutageProvenance.held_block_origin (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {B : NamedBlock V} (hB : B ∈ (W i v).st.bodies) :
    B = NamedBlock.genesis ∨
      ∃ j : Nat, j < i ∧ ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j v (.block B) t := by
  revert hB
  induction i with
  | zero =>
    intro hB
    left
    have h0 : W 0 = fun v' => M.initial S v' := (hW 0).1
    rw [h0] at hB
    change B ∈ (M.initial S v : M.N).st.bodies at hB
    rw [facts.nd.initial_st, facts.hd.initial_bodies,
      Finset.mem_singleton] at hB
    exact hB
  | succ i ih =>
    intro hB
    by_cases hpre : B ∈ (W i v).st.bodies
    · rcases ih hpre with hgen | ⟨j, hj, t, hacc⟩
      · exact Or.inl hgen
      · exact Or.inr ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), t, hacc⟩
    · obtain ⟨t, hacc⟩ := Restated.Vocabulary.Proofs.NamedReceiptCalls.new_block_accepts facts S rho i v B
        W hW hpre hB
      exact Or.inr ⟨i, Nat.lt_succ_self i, t, hacc⟩

/-- For every path `W` of `rho`, if the full row `a` is in the rows of its round of `v`'s store in
    `W i`, then `v` accepts `a` at some event `j < i` of `rho`, at some time `t`, read along `W`. -/
theorem Vocabulary.Proofs.NamedOutageProvenance.held_row_origin (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {a : NamedAttestation V} (ha : a ∈ (W i v).st.sg_rows a.round) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j v (.attest a) t := by
  revert ha
  induction i with
  | zero =>
    intro ha
    have h0 : W 0 = fun v' => M.initial S v' := (hW 0).1
    rw [h0] at ha
    change a ∈ (M.initial S v : M.N).st.sg_rows a.round at ha
    rw [facts.nd.initial_st, facts.hd.initial_sg_rows] at ha
    simp only [List.not_mem_nil] at ha
  | succ i ih =>
    intro ha
    by_cases hpre : a ∈ (W i v).st.sg_rows a.round
    · obtain ⟨j, hj, t, hacc⟩ := ih hpre
      exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), t, hacc⟩
    · obtain ⟨t, hacc⟩ := Restated.Vocabulary.Proofs.NamedReceiptCalls.new_attestation_accepts facts S rho
        i v a W hW hpre ha
      exact ⟨i, Nat.lt_succ_self i, t, hacc⟩

end

end DecoupledConsensusModel.Sts.Restated
