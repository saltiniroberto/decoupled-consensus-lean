module
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceipt_process
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_process
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
public import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
public import Proofs.Vocabulary.Execution.EmissionShape
public import Proofs.Claims.RunAll
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Proofs.Claims.Spec2Claims.Claim13bModel_initial
public import Proofs.Claims.Spec2Claims.Claim13bModel_author
public import Proofs.Claims.Spec2Claims.Claim13bModel_postCore_mk
public import Proofs.Vocabulary.ModelProperties.NamedNode_process
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceipt_processed
public import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_update_confirmation_with_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
public import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial

@[expose] public section

/-!
# What a store records after a receipt or a tick

A receipt records nothing but its own payload and the objects that payload carries
(`flip_of_process`), and a tick records nothing but what it emits and what an emitted block carries
(`addsOnlyCarried_named_tick`, `addsOnlyCarried_node_tick`). `CarriedCall` is the witness that a
carried object's block entered the store.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The handler call a carried object gets -/

/-- An object reaches a validator inside block `B`: `B` lists the object at some position, and `B`
    entered the store's erased tree (for a Goldfish vote) or its named bodies (for an attestation)
    at `before`. -/
def CarriedCall (S : Setup V) (before : NamedStore V) (B : NamedBlock V) :
    NamedObject V → Prop
  | .block _ => False
  | .gfVote u => (∃ j : Nat, B.gf_votes[j]? = some u) ∧ B.erase ∉ before.core.T ∧
      B.erase ∈ (NamedReceiptCalls.postCore S before B).core.T
  | .attest a => (∃ j : Nat, B.attestations[j]? = some a) ∧ B ∉ before.bodies ∧
      B ∈ (NamedReceiptCalls.postCore S before B).bodies

/-! ## A receipt records only its payload and what the payload carries -/

/-- If a store records `o` after the receipt of `o'` and did not record it before, then `o` is `o'`,
    or `o'` is a block that carries `o` and entered the store there. -/
theorem flip_of_process (S : Setup V) (st : NamedStore V) (o' o : NamedObject V)
    (h0 : NamedReceipt.processed st o = false)
    (h1 : NamedReceipt.processed (NamedReceipt.process S st o') o = true) :
    o = o' ∨ ∃ B : NamedBlock V, o' = .block B ∧ CarriedCall S st B o := by
  cases o' with
  | gfVote u' =>
      have hst : NamedReceipt.process S st (.gfVote u')
          = { st with core := on_goldfish_vote_checked S.E st.core u' } :=
        Proofs.ModelProperties.process_gfVote S st u'
      rw [hst] at h1
      cases o with
      | block C =>
          rw [processed_block_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_block_iff] at h0
          exact absurd h1 h0
      | attest a =>
          rw [processed_attest_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_attest_iff] at h0
          exact absurd h1 h0
      | gfVote u =>
          rw [processed_gfVote_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_gfVote_iff] at h0
          have h1' : u ∈ (on_goldfish_vote_checked S.E st.core u').gf_votes u.slot := h1
          rcases mem_gf_votes_on_goldfish_vote_checked S.E st.core u' u.slot h1' with h | h
          · exact absurd h h0
          · exact Or.inl (by rw [h])
  | attest a' =>
      have hst : NamedReceipt.process S st (.attest a')
          = NamedAdmission.admit_row S.hc st a' := Proofs.ModelProperties.process_attest S st a'
      rw [hst] at h1
      cases o with
      | block C =>
          rw [processed_block_iff, admit_row_bodies] at h1
          rw [Bool.eq_false_iff, Ne, processed_block_iff] at h0
          exact absurd h1 h0
      | gfVote u =>
          rw [processed_gfVote_iff, admit_row_gf_votes] at h1
          rw [Bool.eq_false_iff, Ne, processed_gfVote_iff] at h0
          exact absurd h1 h0
      | attest a =>
          rw [processed_attest_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_attest_iff] at h0
          rcases mem_sg_rows_admit_row S.hc st a' a.round h1 with h | h
          · exact absurd h h0
          · exact Or.inl (by rw [h])
  | block B =>
      have hst : NamedReceipt.process S st (.block B)
          = NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B :=
        Proofs.ModelProperties.process_block S st B
      rw [hst] at h1
      cases o with
      | block C =>
          rw [processed_block_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_block_iff] at h0
          rcases on_block_with_bodies_upper .alsoCarried S.E S.hc S.cfg st B C h1 with h | h
          · exact absurd h h0
          · exact Or.inl (by rw [h])
      | gfVote u =>
          rw [processed_gfVote_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_gfVote_iff] at h0
          rcases on_block_with_gf_votes_upper .alsoCarried S.E S.hc S.cfg st B u.slot u h1
            with h | ⟨hmem, hnotT, hT⟩
          · exact absurd h h0
          · exact Or.inr ⟨B, rfl, List.getElem?_of_mem hmem, hnotT,
              by rw [postCore_core_T_eq]; exact hT⟩
      | attest a =>
          rw [processed_attest_iff] at h1
          rw [Bool.eq_false_iff, Ne, processed_attest_iff] at h0
          rcases on_block_with_sg_rows_upper .alsoCarried S.E S.hc S.cfg st B a.round a h1
            with h | ⟨hmem, hnotb, hb⟩
          · exact absurd h h0
          · exact Or.inr ⟨B, rfl, List.getElem?_of_mem hmem, hnotb,
              by rw [postCore_bodies_eq]; exact hb⟩

/-! ## Chaining the stages of a tick -/

/-- Going from store `a` to store `b` keeps everything recorded, and whatever `b` newly records is
    one of the objects in `es`. -/
def AddsOnly (a b : NamedStore V) (es : List (NamedObject V)) : Prop :=
  (∀ o : NamedObject V, NamedReceipt.processed a o = true →
      NamedReceipt.processed b o = true) ∧
    ∀ o : NamedObject V, NamedReceipt.processed a o = false →
      NamedReceipt.processed b o = true → o ∈ es

/-- Going from store `a` to store `b` keeps everything recorded, and whatever `b` newly records is
    in `es` or is carried by a block in `es` that entered the store at `a`. -/
def AddsOnlyCarried (S : Setup V) (a b : NamedStore V) (es : List (NamedObject V)) : Prop :=
  (∀ o : NamedObject V, NamedReceipt.processed a o = true →
      NamedReceipt.processed b o = true) ∧
    ∀ o : NamedObject V, NamedReceipt.processed a o = false →
      NamedReceipt.processed b o = true →
      o ∈ es ∨ ∃ B : NamedBlock V, NamedObject.block B ∈ es ∧ CarriedCall S a B o

omit [Fintype V] in
theorem AddsOnly.refl (a : NamedStore V) (es : List (NamedObject V)) : AddsOnly a a es :=
  ⟨fun _ h => h, fun o h h' => absurd (h.symm.trans h') (by simp)⟩

theorem AddsOnlyCarried.refl (S : Setup V) (a : NamedStore V) (es : List (NamedObject V)) :
    AddsOnlyCarried S a a es :=
  ⟨fun _ h => h, fun o h h' => absurd (h.symm.trans h') (by simp)⟩

omit [Fintype V] in
theorem AddsOnly.mono {a b : NamedStore V} {es es' : List (NamedObject V)}
    (h : AddsOnly a b es) (hs : ∀ o ∈ es, o ∈ es') : AddsOnly a b es' :=
  ⟨h.1, fun o h0 h1 => hs o (h.2 o h0 h1)⟩

theorem AddsOnlyCarried.mono (S : Setup V) {a b : NamedStore V}
    {es es' : List (NamedObject V)} (h : AddsOnlyCarried S a b es)
    (hs : ∀ o ∈ es, o ∈ es') : AddsOnlyCarried S a b es' :=
  ⟨h.1, fun o h0 h1 => (h.2 o h0 h1).imp (hs o) (fun ⟨B, hB, hc⟩ => ⟨B, hs _ hB, hc⟩)⟩

/-- Two steps in a row record nothing outside `es`, the carried witness taken at the first step's
    starting store. -/
theorem AddsOnlyCarried.trans (S : Setup V) {a b c : NamedStore V}
    {es : List (NamedObject V)} (h1 : AddsOnlyCarried S a b es) (h2 : AddsOnly b c es) :
    AddsOnlyCarried S a c es := by
  refine ⟨fun o h => h2.1 o (h1.1 o h), fun o h0 h1' => ?_⟩
  by_cases hb : NamedReceipt.processed b o = true
  · exact h1.2 o h0 hb
  · exact Or.inl (h2.2 o (by simpa using hb) h1')

omit [Fintype V] in
theorem AddsOnly.ite (C : Prop) [Decidable C] {a b : NamedStore V}
    {es : List (NamedObject V)} (h : AddsOnly a b es) :
    AddsOnly a (if C then b else a) (if C then es else []) := by
  split_ifs with hC
  · exact h
  · exact AddsOnly.refl a []

omit [Fintype V] in
theorem AddsOnly.ite_nil (C : Prop) [Decidable C] {a b : NamedStore V}
    (h : AddsOnly a b []) : AddsOnly a (if C then b else a) [] := by
  split_ifs with hC
  · exact h
  · exact AddsOnly.refl a []

theorem AddsOnlyCarried.ite (S : Setup V) (C : Prop) [Decidable C] {a b : NamedStore V}
    {es : List (NamedObject V)} (h : AddsOnlyCarried S a b es) :
    AddsOnlyCarried S a (if C then b else a) (if C then es else []) := by
  split_ifs with hC
  · exact h
  · exact AddsOnlyCarried.refl S a []

theorem AddsOnlyCarried.of_ite (S : Setup V) (C : Prop) [Decidable C]
    {a b c : NamedStore V} {es fs : List (NamedObject V)}
    (h1 : C → AddsOnlyCarried S a b es) (h2 : ¬ C → AddsOnlyCarried S a c fs) :
    AddsOnlyCarried S a (if C then b else c) (if C then es else fs) := by
  split_ifs with hC
  · exact h1 hC
  · exact h2 hC

/-! ## The duties, one stage at a time -/


/-- The named proposal duty records nothing but the block it emits and what that block
    carries. -/
theorem addsOnlyCarried_propose (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) (l : List (NamedObject V))
    (hsome : ∀ B : NamedBlock V,
      (NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).2 = some B →
        l = [NamedObject.block B]) :
    AddsOnlyCarried S st (NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 l := by
  rcases named_propose_cases S gc nd st with h | ⟨B, h⟩
  · rw [h]; exact AddsOnlyCarried.refl S st l
  · rw [h, hsome B (by rw [h])]
    refine ⟨fun o hh => processed_mono_receipt S st o (.block B) hh, fun o h0 h1 => ?_⟩
    rcases flip_of_process S st (.block B) o h0 h1 with hh | ⟨C, hC, hcar⟩
    · exact Or.inl (by rw [hh]; exact List.mem_cons_self)
    · have hCB : C = B := by injection hC.symm
      subst hCB
      exact Or.inr ⟨C, List.mem_cons_self, hcar⟩

/-- The named Goldfish vote duty records nothing but the vote it emits. -/
theorem addsOnly_vote (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) (l : List (NamedObject V))
    (hsome : ∀ u : GoldfishVote V,
      (NamedDuties.goldfish_vote_with gc S.E S.hc nd st).2 = some u →
        l = [NamedObject.gfVote u]) :
    AddsOnly st (NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 l := by
  rcases named_vote_cases S gc nd st with h | ⟨u, h⟩
  · rw [h]; exact AddsOnly.refl st l
  · rw [h, hsome u (by rw [h])]
    refine ⟨fun o hh => processed_mono_receipt S st o (.gfVote u) hh, fun o h0 h1 => ?_⟩
    rcases flip_of_process S st (.gfVote u) o h0 h1 with hh | ⟨B, hB, -⟩
    · rw [hh]; exact List.mem_cons_self
    · exact absurd hB (by simp)

/-- The named confirmation duty records nothing at all. -/
theorem addsOnly_confirmation (gc : GradeContract V) (E : Env V) (hc : HealConfig)
    (st : NamedStore V) (s : Slot) :
    AddsOnly st (NamedDuties.update_confirmation_with gc E hc st s) [] := by
  have hp : ∀ o : NamedObject V,
      NamedReceipt.processed (NamedDuties.update_confirmation_with gc E hc st s) o
        = NamedReceipt.processed st o := by
    intro o; exact processed_update_confirmation_with gc E hc st s o
  refine ⟨fun o h => by rw [hp o]; exact h, fun o h0 h1 => ?_⟩
  rw [hp o, h0] at h1
  exact absurd h1 (by simp)

/-- The named attestation duty records nothing but the row it emits. -/
theorem addsOnly_attest (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) (record : NamedRecord) :
    AddsOnly st (NamedDuties.attest_with gc S.E S.hc nd st record).1
      [NamedObject.attest (NamedDuties.attest_with gc S.E S.hc nd st record).2.2] := by
  have hfst : (NamedDuties.attest_with gc S.E S.hc nd st record).1
      = NamedReceipt.process S st
        (.attest (NamedDuties.attest_with gc S.E S.hc nd st record).2.2) :=
    attest_with_fst_eq_process S gc nd st record
  rw [hfst]
  refine ⟨fun o h => processed_mono_receipt S st o _ h, fun o h0 h1 => ?_⟩
  rcases flip_of_process S st _ o h0 h1 with h | ⟨B, hB, -⟩
  · rw [h]; exact List.mem_cons_self
  · exact absurd hB (by simp)

/-! ## The tick -/

omit [DecidableEq V] [Fintype V] in
theorem fst_ite {α β : Type} (C : Prop) [Decidable C] (x y : α × β) :
    (if C then x else y).1 = if C then x.1 else y.1 := by split <;> rfl

omit [DecidableEq V] [Fintype V] in
theorem snd_ite {α β : Type} (C : Prop) [Decidable C] (x y : α × β) :
    (if C then x else y).2 = if C then x.2 else y.2 := by split <;> rfl

theorem AddsOnlyCarried.chain4 (S : Setup V) {a0 a1 a2 a3 a4 : NamedStore V}
    {e1 e2 e4 : List (NamedObject V)} (h1 : AddsOnlyCarried S a0 a1 e1)
    (h2 : AddsOnly a1 a2 e2) (h3 : AddsOnly a2 a3 []) (h4 : AddsOnly a3 a4 e4) :
    AddsOnlyCarried S a0 a4 (e1 ++ e2 ++ e4) := by
  refine AddsOnlyCarried.trans S (AddsOnlyCarried.trans S (AddsOnlyCarried.trans S
    (AddsOnlyCarried.mono S h1 ?_) (AddsOnly.mono h2 ?_)) (AddsOnly.mono h3 ?_))
    (AddsOnly.mono h4 ?_)
  · intro o ho; simp only [List.mem_append]; tauto
  · intro o ho; simp only [List.mem_append]; tauto
  · intro o ho; exact absurd ho (by simp)
  · intro o ho; simp only [List.mem_append]; tauto

theorem AddsOnlyCarried.chain3 (S : Setup V) {a0 a1 a2 a3 : NamedStore V}
    {e1 e2 : List (NamedObject V)} (h1 : AddsOnlyCarried S a0 a1 e1)
    (h2 : AddsOnly a1 a2 e2) (h3 : AddsOnly a2 a3 []) :
    AddsOnlyCarried S a0 a3 (e1 ++ e2) := by
  refine AddsOnlyCarried.trans S (AddsOnlyCarried.trans S
    (AddsOnlyCarried.mono S h1 ?_) (AddsOnly.mono h2 ?_)) (AddsOnly.mono h3 ?_)
  · intro o ho; simp only [List.mem_append]; tauto
  · intro o ho; simp only [List.mem_append]; tauto
  · intro o ho; exact absurd ho (by simp)

/-- A store records nothing after its tick, beyond what it recorded once the clock was set, except
    the objects the tick emits and those carried by an emitted block. -/
theorem addsOnlyCarried_named_tick (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) (record : NamedRecord) (t : Int) :
    AddsOnlyCarried S (NamedStore.setClock S.E st t)
      (NamedTick.tick gc S.E S.hc S.cfg nd st record t).1
      (NamedTick.tick gc S.E S.hc S.cfg nd st record t).2.2 := by
  classical
  rw [DecoupledConsensusModel.Proofs.NamedTick.tick_computed_duties]
  dsimp only
  simp only [fst_ite, snd_ite]
  refine AddsOnlyCarried.of_ite S _ (fun _ => ?_) (fun _ => ?_)
  · refine AddsOnlyCarried.chain4 S
      (AddsOnlyCarried.ite S _ (addsOnlyCarried_propose S gc nd _ _ ?_))
      (AddsOnly.ite _ (addsOnly_vote S gc nd _ _ ?_))
      (AddsOnly.ite_nil _ (addsOnly_confirmation gc S.E S.hc _ _))
      (addsOnly_attest S gc nd _ _)
    · intro B hB; rw [hB]
    · intro u hu; rw [hu]; rfl
  · refine AddsOnlyCarried.chain3 S
      (AddsOnlyCarried.ite S _ (addsOnlyCarried_propose S gc nd _ _ ?_))
      (AddsOnly.ite _ (addsOnly_vote S gc nd _ _ ?_))
      (AddsOnly.ite_nil _ (addsOnly_confirmation gc S.E S.hc _ _))
    · intro B hB; rw [hB]
    · intro u hu; rw [hu]; rfl

/-- The same for the node transition `NamedNode.tick`, whose store is the named tick's own. -/
theorem addsOnlyCarried_node_tick (S : Setup V) (v : V) (n : NamedNodeState V) (t : Int) :
    AddsOnlyCarried S (NamedStore.setClock S.E n.st t) (NamedNode.tick S v n t).1.st
      (NamedNode.tick S v n t).2 := by
  rw [namedNode_tick_st, namedNode_tick_snd]
  exact addsOnlyCarried_named_tick S _ (S.node v) n.st n.record t

/-! ## A receipt that changes the store records its own payload -/

/-- A receipt either returns the store unchanged, or the store records the receipt's own payload
    afterwards. -/
theorem receipt_noop_or_processed (S : Setup V) (st : NamedStore V) (o' : NamedObject V) :
    NamedReceipt.process S st o' = st ∨
      NamedReceipt.processed (NamedReceipt.process S st o') o' = true := by
  cases o' with
  | block B =>
      rw [Proofs.ModelProperties.process_block]
      rcases on_block_with_noop_or_mem .alsoCarried S.E S.hc S.cfg st B with h | h
      · exact Or.inl h
      · exact Or.inr ((processed_block_iff _ B).2 h)
  | gfVote u =>
      rw [Proofs.ModelProperties.process_gfVote]
      rcases on_goldfish_vote_checked_noop_or_mem S.E st.core u with h | h
      · refine Or.inl ?_
        rw [h]
      · exact Or.inr ((processed_gfVote_iff _ u).2 ((mem_store_pool_iff _ _ _).1 h))
  | attest a =>
      rw [Proofs.ModelProperties.process_attest]
      rcases admit_row_noop_or_mem S.hc st a with h | h
      · exact Or.inl h
      · exact Or.inr ((processed_attest_iff _ a).2 h)

end DecoupledConsensusModel.Sts
