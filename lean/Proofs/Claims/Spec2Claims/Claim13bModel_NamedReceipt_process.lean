module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with_mk

@[expose] public section

/-!
# Facts about `NamedReceipt.process`

The receipt of a delivered object on the named store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceipt.process
  DecoupledConsensusModel.Execution.NamedReceipt.processed
  DecoupledConsensusModel.NamedAttestation.erase DecoupledConsensusModel.Protocol.Store.pool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Delivering a block the store already holds among its bodies leaves the store unchanged. -/
theorem process_block_of_mem_bodies (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hT : st.core.T = st.bodies.image NamedBlock.erase)
    (hB : B ∈ st.bodies) :
    NamedReceipt.process S st (NamedObject.block B) = st := by
  show Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B = st
  simp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried,
    process_block_core_of_mem_bodies S.E S.hc S.cfg st B hT hB]
  rw [if_neg (fun h => h.1 hB)]

/-- Delivering a Goldfish vote the store already holds for that vote's slot leaves the store
    unchanged. -/
theorem process_gfVote_of_mem_pool (S : Setup V) (st : Protocol.NamedStore V)
    (u : GoldfishVote V) (hu : u ∈ st.core.pool u.slot) :
    NamedReceipt.process S st (NamedObject.gfVote u) = st := by
  have hlist : u ∈ st.core.gf_votes u.slot := by
    simpa only [Protocol.Store.pool, List.mem_toFinset] using hu
  show { st with core := Protocol.on_goldfish_vote_checked S.E st.core u } = st
  rw [on_goldfish_vote_checked_of_mem S.E st.core u hlist]

/-- Delivering an attestation the store already holds among its named rows for that round leaves the
    store unchanged. -/
theorem process_attest_of_mem_rows (S : Setup V) (st : Protocol.NamedStore V)
    (a : NamedAttestation V)
    (hPool : ∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase)
    (ha : a ∈ st.sg_rows a.round) :
    NamedReceipt.process S st (NamedObject.attest a) = st := by
  have hmem : a.erase ∈ st.core.sg_pool a.round := by
    simp only [Protocol.Store.sg_pool, List.mem_toFinset, hPool a.round]
    exact List.mem_map_of_mem ha
  have hsg : Protocol.on_sg_vote S.hc st.core a.erase = st.core :=
    on_sg_vote_of_mem_round_votes S.hc st.core a.erase
      (mem_round_votes_of_mem_sg_pool st.core a.erase hmem)
  show Protocol.NamedAdmission.admit_row S.hc st a = st
  simp only [Protocol.NamedAdmission.admit_row, hsg]
  rw [if_neg (fun h => h.1 h.2)]

/-- A receipt only adds to the named bodies, whatever it delivers. -/
theorem receipt_bodies_subset (S : Setup V) (st : NamedStore V) (o' : NamedObject V) :
    st.bodies ⊆ (NamedReceipt.process S st o').bodies := by
  cases o' with
  | block B' =>
      show st.bodies ⊆ (NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B').bodies
      exact on_block_with_bodies_subset .alsoCarried S.E S.hc S.cfg st B'
  | gfVote u => exact Finset.Subset.refl _
  | attest a =>
      show st.bodies ⊆ (NamedAdmission.admit_row S.hc st a).bodies
      rw [admit_row_bodies]

/-- A receipt only adds to the slot vote lists, whatever it delivers. -/
theorem receipt_gf_votes_subset (S : Setup V) (st : NamedStore V) (o' : NamedObject V)
    (k : Slot) :
    st.core.gf_votes k ⊆ (NamedReceipt.process S st o').core.gf_votes k := by
  cases o' with
  | block B' =>
      show st.core.gf_votes k ⊆
        (NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B').core.gf_votes k
      exact on_block_with_gf_votes_subset .alsoCarried S.E S.hc S.cfg st B' k
  | gfVote u =>
      show st.core.gf_votes k ⊆ (on_goldfish_vote_checked S.E st.core u).gf_votes k
      exact on_goldfish_vote_checked_gf_votes_subset S.E st.core u k
  | attest a =>
      show st.core.gf_votes k ⊆ (NamedAdmission.admit_row S.hc st a).core.gf_votes k
      rw [admit_row_gf_votes]
      exact fun _ hy => hy

/-- A receipt only adds to the named row lists, whatever it delivers. -/
theorem receipt_sg_rows_subset (S : Setup V) (st : NamedStore V) (o' : NamedObject V)
    (r : Round) :
    st.sg_rows r ⊆ (NamedReceipt.process S st o').sg_rows r := by
  cases o' with
  | block B' =>
      show st.sg_rows r ⊆
        (NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B').sg_rows r
      exact on_block_with_sg_rows_subset .alsoCarried S.E S.hc S.cfg st B' r
  | gfVote u => exact fun _ h => h
  | attest a =>
      show st.sg_rows r ⊆ (NamedAdmission.admit_row S.hc st a).sg_rows r
      exact admit_row_sg_rows_subset S.hc st a r

/-- Whatever a receipt delivers, an object the store had already recorded is still recorded
    afterwards. -/
theorem processed_mono_receipt (S : Setup V) (st : NamedStore V) (o o' : NamedObject V)
    (h : NamedReceipt.processed st o = true) :
    NamedReceipt.processed (NamedReceipt.process S st o') o = true := by
  cases o with
  | block B =>
      have hB : B ∈ st.bodies := of_decide_eq_true h
      exact decide_eq_true (receipt_bodies_subset S st o' hB)
  | gfVote u =>
      have hu : u ∈ st.core.gf_votes u.slot := List.mem_toFinset.1 (of_decide_eq_true h)
      exact decide_eq_true
        (List.mem_toFinset.2 (receipt_gf_votes_subset S st o' u.slot hu))
  | attest a =>
      have ha : a ∈ st.sg_rows a.round := of_decide_eq_true h
      exact decide_eq_true (receipt_sg_rows_subset S st o' a.round ha)

end DecoupledConsensusModel.Sts
