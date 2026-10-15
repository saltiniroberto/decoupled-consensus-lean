import Proofs.Vocabulary.Execution.ReceiptCallsBase
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Block calls, delivery results and self proposals

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a delivered or
self-proposed block has a block call at its event, read along a path `W` of a run, and every block
call's input satisfies the confirmation-membership invariant; also the store a delivery leaves, and
the proposal duty call behind a block a validator's own tick sends.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsBase
open Execution
open Execution.NamedReceiptCalls

/-- When the `i`-th event of `rho` is the delivery of `B` to `v`, for every path `W` of `rho`, `v`'s
    store in `W i` is the input of a block call of `B` at `v` at that event, read along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_delivery (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v (.block B) t)) :
    ∀ W, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W →
      Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B (W i v).st :=
  fun _ _ => Or.inl ⟨t, hi, rfl⟩

/-- When the `i`-th event of `rho` is `v`'s tick at `t`, for every path `W` of `rho` such that some
    outcome of that tick from `v`'s node state in `W i` has `v`'s node state in `W (i + 1)` as its
    node state and sends `B`, `v`'s store in `W i` with its clock set to `t` is the input of a block
    call of `B` at `v` at that event, read along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsBase.blockCallAt_self (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    ∀ W, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W →
      (∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
        NamedObject.block B ∈ out.2) →
      Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B
        (M.ns_setClock S.E (W i v).st t) :=
  fun _ _ hB => Or.inr ⟨t, hi, hB, rfl⟩

/-- For every path `W` of `rho`, if `before` is the input of a block call of `B` at `v` at the
    `i`-th event of `rho` read along `W`, then `before` satisfies the confirmation-membership
    invariant. -/
theorem Vocabulary.Proofs.NamedReceiptCallsBase.block_call_before_invariant (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {B : NamedBlock V} {before : M.NS} :
    ∀ W, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W →
    Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B before →
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg before := by
  intro W hW h
  have hpre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v (W i)
    (hW i).1).1
  rcases h with ⟨t, _, hb⟩ | ⟨t, _, _, hb⟩
  · rw [hb]
    exact hpre
  · rw [hb]
    exact facts.hd.invariant_clock S.E S.cfg _ t hpre

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsBase
open Execution
open Execution.NamedReceiptCalls

/-- When the `i`-th event of `rho` is the delivery of `o` to `v`, for every world `w₁` before it in
    which `v`'s receipt of `o` can return something, and every world `w₂` the delivery leads to from
    `w₁`, `v`'s store in `w₂` is `M.make_grades_compatible_with_finalized` of the store
    `M.receipt_process` returns on `v`'s store in `w₁` and `o`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    (∃ n' : M.N, M.process S (w₁ v) o ⇢ n') →
    ∀ w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁,
      (w₂ v).st = M.make_grades_compatible_with_finalized (M.receipt_process S (w₁ v).st o) := by
  intro w₁ hw₁ hproc w₂ hw₂
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hi w₁ hw₁ w₂ hw₂
    with h | ⟨hno, -⟩
  · exact facts.nd.process_st S (w₁ v) o (w₂ v) h
  · obtain ⟨n', hn'⟩ := hproc
    exact absurd hn' (hno n')

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsBase
open Execution
open Execution.NamedReceiptCalls

/-- When the `i`-th event of `rho` is `v`'s tick at `t`, for every world `w` before it, every
    outcome `out` of that tick from `v`'s node state in `w` that sends the block `B`, and every
    outcome `c` of `M.onPhaseTick` at `t` on `v`'s store and cache in `w`, every outcome `D` of the
    proposal duty, run with the frame contract of `c` on `v`'s store in `w` with its clock set to
    `t`, is the store the block handler returns on `B` (with the attestations included in `B`
    received too), with the grade cache `M.contractCache (M.frameContract c)` written into it,
    together with `B`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {t : Time} {B : NamedBlock V}
    (hi : rho.events[i]? = some (.tick v t)) :
    ∀ w ∈ Record.stateBeforeOf M S rho i,
    ∀ out : M.N × List (NamedObject V), M.tick S v (w v) t ⇢ out →
    NamedObject.block B ∈ out.2 →
    let n := w v
    let before := M.ns_setClock S.E n.st t
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
    ∀ D : M.NS × Option (NamedBlock V),
      M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v) before ⇢ D →
      D = (M.store_with_cache (M.on_block_with .alsoCarried S.E S.hc S.cfg before B)
        (M.contractCache (M.frameContract c)), some B) := by
  intro w hw out hout hB
  dsimp only
  intro c hc D hD
  have _hr : M.reachedNode (w v) := facts.ndRun.stateBeforeOf_reachedNode S rho i w hw v
  have _hv : M.runs_as (w v) v := facts.ndRun.stateBeforeOf_runs_as S rho i w hw v
  have _hrs : M.reachedStore (M.ns_setClock S.E (w v).st t) :=
    facts.sto.reachedStore_setClock S.E _ t (facts.nd.reachedStore_of_node _ _hr)
  exact facts.dt.propose_block_with_eq_of_snd _ _ _ _ _ _ D hD
    ((facts.nd.block_mem_on_tick_emit S v (w v) t out hout hB).2 c hc D hD)

end

end DecoupledConsensusModel.Sts.Restated
