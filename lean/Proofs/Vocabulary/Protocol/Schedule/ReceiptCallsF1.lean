module
public import Proofs.Vocabulary.Protocol.Handlers.Admission
public import Proofs.Vocabulary.ModelProperties.NamedNode_process
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
public import Proofs.Vocabulary.ModelProperties.NamedReceiptCalls_postCore
public import Proofs.Vocabulary.ModelProperties.NamedAdmission_admit_carried
import Proofs.Vocabulary.Execution.Runtime
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Receipt of SG rows

Facts about the calls of `admit_row`, alone and in the fold over a block's included rows: which row
a call can add, the call that adds a new row, and the receipt stamp it sets.
-/
namespace DecoupledConsensusModel.Proofs.NamedReceiptCallsF1
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- A row in the store after `admit_row` was already there or is the incoming row. -/
theorem admit_row_mem_cases (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V)
    (h : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows a.round) :
    a ∈ st.sg_rows a.round ∨ a = incoming := by
  dsimp only [Protocol.NamedAdmission.admit_row] at h
  split_ifs at h <;> aesop

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
theorem admit_row_mem_mono (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (h : a ∈ st.sg_rows a.round) :
    a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows a.round := by
  dsimp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> by_cases hr : a.round = incoming.round <;> simp_all

set_option linter.unusedFintypeInType false in
theorem admit_rows_mem_mono (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (a : NamedAttestation V)
    (h : a ∈ st.sg_rows a.round) :
    a ∈ (Protocol.NamedAdmission.admit_rows hc st rows).sg_rows a.round := by
  induction rows generalizing st with
  | nil => exact h
  | cons row rows ih => exact ih _ (admit_row_mem_mono hc st row a h)

set_option linter.unusedFintypeInType false in
/-- A row new to the store after `admit_rows` was added by the call on that row at some index `j` of
    `rows`, after the first `j` calls left it absent. -/
theorem admit_rows_new_marker (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (a : NamedAttestation V)
    (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_rows hc st rows).sg_rows a.round) :
    ∃ j, j < rows.length ∧ rows[j]? = some a ∧
      a ∉ (Protocol.NamedAdmission.admit_rows hc st (rows.take j)).sg_rows a.round ∧
      a ∈ (Protocol.NamedAdmission.admit_row hc
        (Protocol.NamedAdmission.admit_rows hc st (rows.take j)) a).sg_rows a.round := by
  induction rows generalizing st with
  | nil => exact False.elim (hpre hpost)
  | cons row rows ih =>
    by_cases hmid : a ∈ (Protocol.NamedAdmission.admit_row hc st row).sg_rows a.round
    · have heq : a = row := (admit_row_mem_cases hc st row a hmid).resolve_left hpre
      subst row
      exact ⟨0, Nat.zero_lt_succ _, rfl, hpre, hmid⟩
    · obtain ⟨j, hj, hrow, hbefore, hafter⟩ :=
        ih (Protocol.NamedAdmission.admit_row hc st row) hmid hpost
      refine ⟨j + 1, Nat.succ_lt_succ hj, ?_, ?_, ?_⟩
      · exact hrow
      · simpa only [List.take_succ_cons, Protocol.NamedAdmission.admit_rows,
          List.foldl_cons] using hbefore
      · simpa only [List.take_succ_cons, Protocol.NamedAdmission.admit_rows,
          List.foldl_cons] using hafter

omit [DecidableEq V] [Fintype V] in
private theorem rows_split_at (rows : List (NamedAttestation V)) (j : Nat)
    (a : NamedAttestation V) (h : rows[j]? = some a) :
    rows = rows.take j ++ a :: rows.drop (j + 1) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop j rows]
  rw [List.drop_eq_getElem_cons hj, hget]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- The fold over a block's included rows reaches the `j`-th row and calls `admit_row` on it once
    before the remaining rows. -/
theorem carried_call_prefix (hc : Protocol.HealConfig)
    (before postCore : Protocol.NamedStore V) (B : NamedBlock V)
    (j : Nat) (a : NamedAttestation V)
    (hnew : B ∉ before.bodies) (hheld : B ∈ postCore.bodies)
    (hrow : B.attestations[j]? = some a) :
    Protocol.NamedAdmission.admit_carried .alsoCarried hc before postCore B =
      Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc
          (Protocol.NamedAdmission.admit_rows hc postCore (B.attestations.take j)) a)
        (B.attestations.drop (j + 1)) :=
  NamedAdmission.carried_row_prefix hc before postCore B _ _ a
    (rows_split_at B.attestations j a hrow) hnew hheld

omit [Fintype V] in
private theorem full_new_core_guard (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_row hc st a).sg_rows a.round) :
    a.erase ∉ st.core.sg_pool a.round ∧
      a.erase ∈ (Protocol.on_sg_vote hc st.core a.erase).sg_pool a.round := by
  by_contra hguard
  have hs : (Protocol.NamedAdmission.admit_row hc st a).sg_rows = st.sg_rows := by
    simp only [Protocol.NamedAdmission.admit_row, if_neg hguard]
  exact hpre (hs ▸ hpost)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- When `admit_row` adds the new row `a`, the receipt stamp of `a`'s SG vote is the store's clock. -/
theorem full_new_row_stamp (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_row hc st a).sg_rows a.round) :
    (Protocol.NamedAdmission.admit_row hc st a).core.timestamp_sg_vote (Protocol.sgVote a.erase) =
      some (st.core.t : Stamp) := by
  obtain ⟨hbefore, hafter⟩ := full_new_core_guard hc st a hpre hpost
  exact NamedAdmission.admitted_receipt_stamp hc st a hbefore hafter

set_option linter.unusedFintypeInType false in
/-- The receipt stamp set when `a` is added is unchanged by the later calls of the fold. -/
theorem full_new_row_stamp_after_suffix (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (suffix : List (NamedAttestation V))
    (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedAdmission.admit_row hc st a).sg_rows a.round) :
    (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st a) suffix).core.timestamp_sg_vote
        (Protocol.sgVote a.erase) = some (st.core.t : Stamp) := by
  have hguard := full_new_core_guard hc st a hpre hpost
  rw [NamedAdmission.admit_rows_core]
  rw [CarriedAdmission.fold_rows_preserve_existing_stamp hc
    (suffix.map NamedAttestation.erase) (Protocol.NamedAdmission.admit_row hc st a).core a.erase
    (by rw [NamedAdmission.admit_row_core]; exact hguard.2)]
  exact full_new_row_stamp hc st a hpre hpost

private theorem post_core_rows (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V) : (Execution.NamedReceiptCalls.postCore S before B).sg_rows = before.sg_rows := by
  dsimp only [Execution.NamedReceiptCalls.postCore, Protocol.NamedStore.process_block_core]
  split_ifs <;> first | rfl | exact NamedStore.commit_rows before _ B

/-- An actual call on the `j`-th included row of `B` fixes the row and the store the call reads; the
    call may reject the row. -/
theorem actual_carried_call (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : Protocol.NamedStore V)
    (h : Execution.NamedReceiptCalls.carriedAttestationAt S rho i v B j a before) :
    Execution.NamedReceiptCalls.blockCallAt S rho i v B before ∧
    B ∉ before.bodies ∧ B ∈ (Execution.NamedReceiptCalls.postCore S before B).bodies ∧
    B.attestations[j]? = some a ∧
    Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B =
      Protocol.NamedAdmission.admit_rows S.hc
        (Protocol.NamedAdmission.admit_row S.hc (Execution.NamedReceiptCalls.f1Input S before B j) a)
        (B.attestations.drop (j + 1)) := by
  rcases h with ⟨hcall, hnew, hheld, hrow⟩
  refine ⟨hcall, hnew, hheld, hrow, ?_⟩
  rw [ModelProperties.on_block_with_eq_admit_rows_postCore S before B hnew hheld,
    ← ModelProperties.admit_carried_of_new .alsoCarried S.hc hnew hheld]
  exact carried_call_prefix S.hc before (Execution.NamedReceiptCalls.postCore S before B) B j a
    hnew hheld hrow

/-- A row new to the store after an actual block call was added by one indexed call on a row the
    block includes. -/
theorem block_full_marker_origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : Protocol.NamedStore V) (a : NamedAttestation V)
    (hcall : Execution.NamedReceiptCalls.blockCallAt S rho i v B before)
    (hpre : a ∉ before.sg_rows a.round)
    (hpost : a ∈ (Execution.NamedReceipt.process S before (.block B)).sg_rows a.round) :
    ∃ j, Execution.NamedReceiptCalls.carriedAttestationAt S rho i v B j a before ∧
      a ∉ (Execution.NamedReceiptCalls.f1Input S before B j).sg_rows a.round ∧
      a ∈ (Protocol.NamedAdmission.admit_row S.hc
        (Execution.NamedReceiptCalls.f1Input S before B j) a).sg_rows a.round := by
  have hcorepre : a ∉ (Execution.NamedReceiptCalls.postCore S before B).sg_rows a.round := by
    rwa [post_core_rows]
  rw [ModelProperties.process_block] at hpost
  have hgate : B ∉ before.bodies ∧ B ∈ (Execution.NamedReceiptCalls.postCore S before B).bodies := by
    by_contra hn
    rw [ModelProperties.on_block_with_eq_postCore_of_not_new S before B hn] at hpost
    exact hcorepre hpost
  rw [ModelProperties.on_block_with_eq_admit_rows_postCore S before B hgate.1 hgate.2] at hpost
  obtain ⟨j, _, hrow, hbefore, hafter⟩ :=
    admit_rows_new_marker S.hc (Execution.NamedReceiptCalls.postCore S before B)
      B.attestations a hcorepre hpost
  exact ⟨j, ⟨hcall, hgate.1, hgate.2, hrow⟩, hbefore, hafter⟩

/-- The input of an actual call on an included row has the block caller's clock and slot. -/
theorem actual_f1_clock (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : Protocol.NamedStore V)
    (_h : Execution.NamedReceiptCalls.carriedAttestationAt S rho i v B j a before) :
    (Execution.NamedReceiptCalls.f1Input S before B j).core.t = before.core.t ∧
      (Execution.NamedReceiptCalls.f1Input S before B j).core.s = before.core.s :=
  ⟨(NamedAdmission.admit_rows_clock S.hc (Execution.NamedReceiptCalls.postCore S before B)
      (B.attestations.take j)).1.trans (ModelProperties.postCore_clock S before B).1,
    (NamedAdmission.admit_rows_clock S.hc (Execution.NamedReceiptCalls.postCore S before B)
      (B.attestations.take j)).2.trans (ModelProperties.postCore_clock S before B).2⟩


/-- At an actual delivery, a row new to the store is the delivered row itself or was added by an
    indexed call on a row of the delivered block; the recipient's clock is unchanged. -/
theorem delivered_full_marker_origin (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (o : NamedObject V) (t : Time) (a : NamedAttestation V)
    (he : rho.events[i]? = some (.deliver v o t))
    (hpre : a ∉ (NamedRun.stateBefore S rho i v).st.sg_rows a.round)
    (hpost : a ∈ (NamedRun.stateBefore S rho (i + 1) v).st.sg_rows a.round) :
    o = .attest a ∨ ∃ B j,
      o = .block B ∧ Execution.NamedReceiptCalls.carriedAttestationAt S rho i v B j a
        (NamedRun.stateBefore S rho i v).st ∧
      a ∉ (Execution.NamedReceiptCalls.f1Input S (NamedRun.stateBefore S rho i v).st B j).sg_rows a.round ∧
      a ∈ (Protocol.NamedAdmission.admit_row S.hc
        (Execution.NamedReceiptCalls.f1Input S (NamedRun.stateBefore S rho i v).st B j) a).sg_rows
          a.round := by
  rw [Proofs.NamedRuntime.stateBefore_deliver S rho he] at hpost
  rw [ModelProperties.process_st] at hpost
  cases o with
  | gfVote u =>
    rw [ModelProperties.process_gfVote] at hpost
    exact False.elim (hpre hpost)
  | attest row =>
    rw [ModelProperties.process_attest] at hpost
    have ha := (admit_row_mem_cases S.hc
      (NamedRun.stateBefore S rho i v).st row a hpost).resolve_left hpre
    exact Or.inl (congrArg NamedObject.attest ha.symm)
  | block B =>
    have hcall : Execution.NamedReceiptCalls.blockCallAt S rho i v B (NamedRun.stateBefore S rho i v).st :=
      Or.inl ⟨t, he, rfl⟩
    obtain ⟨j, hcarried, hbefore, hafter⟩ :=
      block_full_marker_origin S rho i v B _ a hcall hpre hpost
    exact Or.inr ⟨B, j, rfl, hcarried, hbefore, hafter⟩

/-- A row new to `v`'s store at a delivery at index `i` was accepted by `v` at that event. -/
theorem delivered_row_accepts (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (o : NamedObject V) (t : Time) (a : NamedAttestation V)
    (he : rho.events[i]? = some (.deliver v o t))
    (hpre : a ∉ (NamedRun.stateBefore S rho i v).st.sg_rows a.round)
    (hpost : a ∈ (NamedRun.stateBefore S rho (i + 1) v).st.sg_rows a.round) :
    NamedRun.acceptsAt S rho i v (.attest a) t := by
  refine ⟨⟨?_, ⟨.deliver v o t, he, rfl, rfl⟩⟩, ?_, ?_⟩
  · change NamedRun.processesAtIndex S rho i v (.attest a) ∨ _
    rcases delivered_full_marker_origin S rho i v o t a he hpre hpost with
      hdirect | ⟨B, j, _, hcarried, _, _⟩
    · subst o
      exact Or.inl (Or.inr ⟨t, he⟩)
    · exact Or.inr ⟨B, j, (NamedRun.stateBefore S rho i v).st, hcarried⟩
  · exact (ModelProperties.processed_attest_eq_false_iff _ a).mpr hpre
  · exact (ModelProperties.processed_attest_eq_true_iff _ a).mpr hpost


private theorem proposal_new_row (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.sg_rows a.round) :
    ∃ B, (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).2 = some B ∧
      a ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).sg_rows a.round := by
  unfold Protocol.NamedDuties.propose_block_with at hpost ⊢
  split at hpost
  · exact False.elim (hpre hpost)
  · rename_i B hB
    exact ⟨B, by simp only, hpost⟩

/-- A row new after a named tick is the tick's emitted attestation, or was added by the block
    handler, run on the clock-updated store, for a block the tick emits. -/
theorem tick_new_full_row_origin (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round)
    (hpost : a ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.sg_rows a.round) :
    NamedObject.attest a ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 ∨
      ∃ B, NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 ∧
        a ∉ (Protocol.NamedStore.setClock E st t).sg_rows a.round ∧
        a ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg
          (Protocol.NamedStore.setClock E st t) B).sg_rows a.round := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time E s then
      (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
      Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have hrows : st3.sg_rows = st1.sg_rows := by
    have hgf (x : Protocol.NamedStore V) := (NamedDuties.goldfish_vote_metadata gc E hc nd x).2
    have hconf (x : Protocol.NamedStore V) (k : Slot) :=
      (NamedDuties.confirmation_metadata gc E hc x k).2
    dsimp only [st3, st2]
    split_ifs <;> simp only [hgf, hconf]
  have hstore : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 =
      (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  have hlocal : a ∈ st3.sg_rows a.round ∨
      NamedObject.attest a ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
    rw [hstore] at hpost
    by_cases hA : t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true
    · rw [if_pos hA] at hpost
      rcases admit_row_mem_cases hc st3
          (Protocol.NamedDuties.attest_with gc E hc nd st3 record).2.2 a hpost with hold | hrow
      · exact Or.inl hold
      · right
        rw [hrow, NamedTick.tick_computed_duties]
        dsimp only [st3, st2, st1, st0, s] at hA ⊢
        simp only [if_pos hA, List.mem_append, List.mem_singleton, or_true]
    · rw [if_neg hA] at hpost
      exact Or.inl hpost
  rcases hlocal with hold | hemitted
  · rw [hrows] at hold
    by_cases hP : 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
    · have hprop : a ∈
          (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0).1.sg_rows a.round := by
        simpa only [st1, if_pos hP] using hold
      obtain ⟨B, hB, hbody⟩ := proposal_new_row gc E hc cfg nd st0 a hpre hprop
      refine Or.inr ⟨B, ?_, hpre, hbody⟩
      rw [NamedTick.tick_computed_duties]
      dsimp only
      dsimp only [st0] at hB
      simp only [hB]
      split_ifs <;> simp only [List.mem_append, List.mem_singleton, true_or]
    · have hfalse : a ∈ st.sg_rows a.round := by
        simpa only [st1, if_neg hP, st0, Protocol.NamedStore.setClock] using hold
      exact False.elim (hpre hfalse)
  · exact Or.inl hemitted

#print axioms admit_row_mem_cases
#print axioms admit_row_mem_mono
#print axioms admit_rows_mem_mono
#print axioms admit_rows_new_marker
#print axioms carried_call_prefix
#print axioms full_new_row_stamp
#print axioms full_new_row_stamp_after_suffix
#print axioms actual_carried_call
#print axioms block_full_marker_origin
#print axioms actual_f1_clock
#print axioms delivered_full_marker_origin
#print axioms delivered_row_accepts
#print axioms tick_new_full_row_origin
end DecoupledConsensusModel.Proofs.NamedReceiptCallsF1

end
