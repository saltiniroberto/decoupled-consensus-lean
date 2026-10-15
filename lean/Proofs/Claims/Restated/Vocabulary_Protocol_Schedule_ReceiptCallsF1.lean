import Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_CarriedAdmissionChecks
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# The calls behind a new attestation row

A new attestation row in a store after a tick, a block call or a delivery comes from a direct row or
from the admission of an attestation included in a block, stated over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- If `B` is new to `before`, held in `postCore`, and its `j`-th attestation is `a`, then admitting
    `B`'s attestations into `postCore` is admitting its first `j` attestations, then `a`, then the
    remaining ones. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.carried_call_prefix (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (before postCore : M.NS) (B : NamedBlock V)
    (j : Nat) (a : NamedAttestation V)
    (hnew : B ∉ before.bodies) (hheld : B ∈ postCore.bodies)
    (hrow : B.attestations[j]? = some a) :
    M.admit_carried .alsoCarried hc before postCore B =
      M.admit_rows hc
        (M.admit_row hc
          (M.admit_rows hc postCore (B.attestations.take j)) a)
        (B.attestations.drop (j + 1)) := by
  have hsplit : B.attestations = B.attestations.take j ++ a :: B.attestations.drop (j + 1) := by
    obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hrow
    conv_lhs => rw [← List.take_append_drop j B.attestations]
    rw [List.drop_eq_getElem_cons hj, hget]
  exact facts.hd.carried_row_prefix hc before postCore B _ _ a hsplit hnew hheld

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- For every path `W` of `rho`, if the `j`-th attestation `a` included in `B` is carried by the
    block call of `B` at `v` at the `i`-th event of `rho` read along `W`, with input `before`, then
    that block call holds, `B` is new to `before` and held after the core call, `a` is the `j`-th
    attestation of `B`, and the block handler on `before` and `B` returns the admission of `a` into
    the `j`-th input followed by the remaining rows. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.actual_carried_call (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : M.NS)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (h : Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt M S rho W i v B j a before) :
    Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B before ∧
    B ∉ before.bodies ∧ B ∈ (M.postCore S before B).bodies ∧
    B.attestations[j]? = some a ∧
    M.on_block_with .alsoCarried S.E S.hc S.cfg before B =
      M.admit_rows S.hc
        (M.admit_row S.hc (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B j) a)
        (B.attestations.drop (j + 1)) := by
  rcases h with ⟨hcall, hnew, hheld, hrow⟩
  refine ⟨hcall, hnew, hheld, hrow, ?_⟩
  rw [facts.nd.on_block_with_eq_admit_rows_postCore S before B hnew hheld,
    ← facts.hd.admit_carried_of_new .alsoCarried S.hc hnew hheld]
  exact Restated.Vocabulary.Proofs.NamedReceiptCallsF1.carried_call_prefix facts S.hc before (M.postCore S before B) B j a
    hnew hheld hrow

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- For every path `W` of `rho`, if `before` is the input of the block call of `B` at `v` at the
    `i`-th event of `rho` read along `W`, and the full row `a` is not in `before`'s rows of its
    round but is in those of the store the receipt of `B` returns on `before`, then for some `j` the
    `j`-th attestation of `B` is `a`, carried by that call, and `a` is not in the `j`-th input's
    rows but is in the rows its admission returns. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.block_full_marker_origin (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : M.NS) (a : NamedAttestation V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B before)
    (hpre : a ∉ before.sg_rows a.round)
    (hpost : a ∈ (M.receipt_process S before (.block B)).sg_rows a.round) :
    ∃ j, Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt M S rho W i v B j a before ∧
      a ∉ (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B j).sg_rows a.round ∧
      a ∈ (M.admit_row S.hc
        (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B j) a).sg_rows a.round := by
  have hcorepre : a ∉ (M.postCore S before B).sg_rows a.round := by
    rwa [facts.nd.postCore_eq_process_block_core, facts.hd.process_block_core_sg_rows_eq]
  rw [facts.nd.process_block] at hpost
  have hgate : B ∉ before.bodies ∧ B ∈ (M.postCore S before B).bodies := by
    by_contra hn
    rw [facts.nd.on_block_with_eq_postCore_of_not_new S before B hn] at hpost
    exact hcorepre hpost
  rw [facts.nd.on_block_with_eq_admit_rows_postCore S before B hgate.1 hgate.2] at hpost
  obtain ⟨j, _, hrow, hbefore, hafter⟩ :=
    facts.hd.admit_rows_new_marker S.hc (M.postCore S before B)
      B.attestations a hcorepre hpost
  exact ⟨j, ⟨hcall, hgate.1, hgate.2, hrow⟩, hbefore, hafter⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- For every path `W` of `rho`, if the `j`-th attestation `a` included in `B` is carried by the
    block call of `B` at `v` at the `i`-th event of `rho` read along `W`, with input `before`, then
    the `j`-th input has `before`'s clock and slot. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.actual_f1_clock (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : M.NS)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (_h : Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt M S rho W i v B j a before) :
    (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B j).core.t = before.core.t ∧
      (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B j).core.s = before.core.s :=
  ⟨(Restated.Vocabulary.Proofs.NamedAdmission.admit_rows_clock facts S.hc (M.postCore S before B)
      (B.attestations.take j)).1.trans (facts.nd.postCore_clock S before B).1,
    (Restated.Vocabulary.Proofs.NamedAdmission.admit_rows_clock facts S.hc (M.postCore S before B)
      (B.attestations.take j)).2.trans (facts.nd.postCore_clock S before B).2⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- When the `i`-th event of `rho` is the delivery of `o` to `v` at `t`, for every path `W` of
    `rho`, if the full row `a` is not in the rows of its round of `v`'s store in `W i` and is in
    those of `v`'s store in `W (i + 1)`, then `o` is the row `a`, or `o` is a block `B` whose call
    at that event read along `W`, with input `v`'s store in `W i`, carries `a` as its `j`-th
    attestation for some `j`, with `a` not in the rows of the `j`-th input and in the rows its
    admission returns. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.delivered_full_marker_origin (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) (o : NamedObject V) (t : Time) (a : NamedAttestation V)
    (he : rho.events[i]? = some (.deliver v o t)) :
    ∀ W, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W →
    a ∉ (W i v).st.sg_rows a.round →
    a ∈ (W (i + 1) v).st.sg_rows a.round →
    o = .attest a ∨ ∃ B j,
      o = .block B ∧ Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt M S rho W i v B j a
        (W i v).st ∧
      a ∉ (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S (W i v).st B j).sg_rows a.round ∧
      a ∈ (M.admit_row S.hc
        (Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S (W i v).st B j) a).sg_rows
          a.round := by
  intro W hW hpre hpost
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) (hW i).1
      (W (i + 1)) (hW i).2
    with hproc | ⟨-, hsame⟩
  · rw [facts.nd.process_st S (W i v) o (W (i + 1) v) hproc,
      facts.nd.make_grades_compatible_with_finalized_sg_rows] at hpost
    cases o with
    | gfVote u =>
      rw [facts.nd.process_gfVote, facts.hd.ns_with_core_sg_rows S.E _ u _ rfl] at hpost
      exact False.elim (hpre hpost)
    | attest row =>
      rw [facts.nd.process_attest] at hpost
      have ha := (facts.hd.admit_row_mem_cases S.hc (W i v).st row a hpost).resolve_left hpre
      exact Or.inl (congrArg NamedObject.attest ha.symm)
    | block B =>
      have hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B
          (W i v).st :=
        Or.inl ⟨t, he, rfl⟩
      obtain ⟨j, hcarried, hbefore, hafter⟩ :=
        Restated.Vocabulary.Proofs.NamedReceiptCallsF1.block_full_marker_origin facts S rho i v B _ a
          W hW hcall hpre hpost
      exact Or.inr ⟨B, j, rfl, hcarried, hbefore, hafter⟩
  · rw [hsame] at hpost
    exact False.elim (hpre hpost)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- When the `i`-th event of `rho` is the delivery of `o` to `v` at `t`, for every path `W` of
    `rho`, if the full row `a` is not in the rows of its round of `v`'s store in `W i` and is in
    those of `v`'s store in `W (i + 1)`, then `v` accepts `a` at the `i`-th event, at time `t`, read
    along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.delivered_row_accepts (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) (o : NamedObject V) (t : Time) (a : NamedAttestation V)
    (he : rho.events[i]? = some (.deliver v o t))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hpre : a ∉ (W i v).st.sg_rows a.round)
    (hpost : a ∈ (W (i + 1) v).st.sg_rows a.round) :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.attest a) t := by
  refine ⟨⟨?_, ⟨.deliver v o t, he, rfl, rfl⟩⟩, ?_, ?_⟩
  · rcases Restated.Vocabulary.Proofs.NamedReceiptCallsF1.delivered_full_marker_origin facts S rho i v o t a
        he W hW hpre hpost with
      hdirect | ⟨B, j, _, hcarried, _, _⟩
    · subst o
      exact Or.inl (Or.inr ⟨t, he⟩)
    · exact Or.inr ⟨B, j, (W i v).st, hcarried⟩
  · exact decide_eq_false hpre
  · exact decide_eq_true hpost

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, if the named attestation
    `a` is not among the rows of its round in `n`'s store and is among them in `out`'s store, then
    either `out` sends the attestation `a`, or `out` sends a block `B` such that `a` is not among
    the rows of `n`'s store with its clock set to `t` and is among the rows of the store the block
    handler returns on that store and `B`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsF1.tick_new_full_row_origin (facts : Record.Facts M) (S : Setup V)
    (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (a : NamedAttestation V) (hpre : a ∉ n.st.sg_rows a.round)
    (hpost : a ∈ out.1.st.sg_rows a.round) :
    NamedObject.attest a ∈ out.2 ∨
      ∃ B, NamedObject.block B ∈ out.2 ∧
        a ∉ (M.ns_setClock S.E n.st t).sg_rows a.round ∧
        a ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg
          (M.ns_setClock S.E n.st t) B).sg_rows a.round :=
  facts.nd.tick_new_full_row_origin S v n t out hout a hpre hpost

end

end DecoupledConsensusModel.Sts.Restated
