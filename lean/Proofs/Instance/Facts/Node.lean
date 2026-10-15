import Proofs.Instance.Model
import Proofs.Instance.Facts.SubtypeEqualities
import Proofs.Instance.Facts.Handlers
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# The node facts at `Model.specDraft`

Proofs of fields of `NodeFacts` and `NodeRunFacts` at the model `Model.specDraft`, one theorem
`specDraft_<field>` per field. The receipt facts are read off `Keeps`, which every admission routine
satisfies; the facts of the initial node state hold by computation; the tick's facts are read off a
run of the tick, step by step.
-/

set_option autoImplicit false

namespace SpecDraftRecord.NodeFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The admission routines, the receipt and the initial node state -/

omit [Inhabited V] in
/-- The spec's `Protocol.on_goldfish_vote_checked` writes only `gf_votes` and `timestamp_vote`. -/
theorem on_goldfish_vote_checked_frame (P : Spec.Provisional V)
    (st : Spec.Store V) (u : Spec.GoldfishVote V) :
    ∃ gv tv, Spec.Protocol.on_goldfish_vote_checked P st u =
      { st with gf_votes := gv, timestamp_vote := tv } := by
  simp only [Spec.Protocol.on_goldfish_vote_checked,
    Spec.Protocol.on_goldfish_vote, Id.run, pure]
  split_ifs <;> exact ⟨_, _, rfl⟩

omit [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.admit_attestation` writes only `attestations` and `timestamp_sg_vote`. -/
theorem admit_attestation_frame (C : Spec.Config) (st : Spec.Store V)
    (a : Spec.Attestation V) :
    ∃ at' ts, Spec.Protocol.admit_attestation C st a =
      { st with attestations := at', timestamp_sg_vote := ts } := by
  simp only [Spec.Protocol.admit_attestation, Spec.Protocol.add_attestation,
    Id.run, pure]
  split_ifs <;> exact ⟨_, _, rfl⟩

omit [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.admit_attestations` writes only `attestations` and `timestamp_sg_vote`. -/
theorem admit_attestations_frame (C : Spec.Config) (st : Spec.Store V)
    (rows : List (Spec.Attestation V)) :
    ∃ at' ts, Spec.Protocol.admit_attestations C st rows =
      { st with attestations := at', timestamp_sg_vote := ts } := by
  simp only [Spec.Protocol.admit_attestations, Id.run,
    List.forIn_pure_yield_eq_foldl]
  induction rows generalizing st with
  | nil => exact ⟨_, _, rfl⟩
  | cons row rows ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, t1, h1⟩ := admit_attestation_frame C st row
    rw [h1]
    obtain ⟨a2, t2, h2⟩ := ih { st with attestations := a1, timestamp_sg_vote := t1 }
    rw [h2]
    exact ⟨_, _, rfl⟩

omit [Inhabited V] in
/-- Admitting a list of Goldfish votes one by one with `Protocol.on_goldfish_vote_checked` writes
    only `gf_votes` and `timestamp_vote`. -/
theorem gf_votes_fold_frame (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (x : Spec.Store V) :
    ∃ gv tv, votes.foldl (fun b a => Spec.Protocol.on_goldfish_vote_checked P b a) x =
      { x with gf_votes := gv, timestamp_vote := tv } := by
  induction votes generalizing x with
  | nil => exact ⟨_, _, rfl⟩
  | cons vote votes ih =>
    simp only [List.foldl_cons]
    obtain ⟨g1, t1, h1⟩ := on_goldfish_vote_checked_frame P x vote
    rw [h1]
    obtain ⟨g2, t2, h2⟩ := ih { x with gf_votes := g1, timestamp_vote := t1 }
    rw [h2]
    exact ⟨_, _, rfl⟩

omit [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.update_finality` writes only `h_max`, `J`, `h_j` and `F`; the new `h_max`
    is at least the old, and the image of the old finalized block is an ancestor of, or equal to,
    the image of the new one. -/
theorem update_finality_frame (st : Spec.Store V) (B : Spec.Block V) :
    ∃ hm J hj F, Spec.Protocol.update_finality st B =
      { st with h_max := hm, J := J, h_j := hj, F := F } ∧ st.h_max ≤ hm ∧
      Block.Preceq st.F.toProof F.toProof := by
  simp only [Spec.Protocol.update_finality, Id.run, pure]
  split_ifs with h1 h2 h3
  · refine ⟨_, _, _, _, rfl, le_max_left _ _, ?_⟩
    simp only [Bool.and_eq_true, Spec.Block.ancestorStrict] at h2
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (Spec.Block.toProof_preceq_of_ancestorEq _ _ h2.1.1.2)
  · exact ⟨_, _, _, _, rfl, le_max_left _ _, Proofs.ModelProperties.Preceq_self _⟩
  · refine ⟨_, _, _, _, rfl, le_max_left _ _, ?_⟩
    simp only [Bool.and_eq_true, Spec.Block.ancestorStrict] at h3
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (Spec.Block.toProof_preceq_of_ancestorEq _ _ h3.1.1.2)
  · exact ⟨_, _, _, _, rfl, le_max_left _ _, Proofs.ModelProperties.Preceq_self _⟩

/-- The store `b` has the clock, the slot, the saved grades and the three confirmation records of
    `a`; its tree holds every block of `a`'s tree; its `h_max` is at least `a`'s; and the image of
    `a`'s finalized block is an ancestor of, or equal to, the image of `b`'s. -/
def Keeps (a b : Spec.Store V) : Prop :=
  b.t = a.t ∧ b.s = a.s ∧ a.T ⊆ b.T ∧ a.h_max ≤ b.h_max ∧ b.saved_grades = a.saved_grades ∧
    b.live_confirmed = a.live_confirmed ∧ b.latest_confirmed = a.latest_confirmed ∧
    b.latest_stable = a.latest_stable ∧ Block.Preceq a.F.toProof b.F.toProof

omit [Fintype V] [Inhabited V] in
/-- `Keeps` is reflexive. -/
theorem Keeps.refl (a : Spec.Store V) : Keeps a a :=
  ⟨rfl, rfl, subset_refl _, le_refl _, rfl, rfl, rfl, rfl, Proofs.ModelProperties.Preceq_self _⟩

omit [Fintype V] [Inhabited V] in
/-- `Keeps` is transitive. -/
theorem Keeps.trans {a b c : Spec.Store V} (h1 : Keeps a b) (h2 : Keeps b c) :
    Keeps a c := by
  obtain ⟨t1, s1, T1, m1, g1, l1, c1, st1, F1⟩ := h1
  obtain ⟨t2, s2, T2, m2, g2, l2, c2, st2, F2⟩ := h2
  exact ⟨t2.trans t1, s2.trans s1, T1.trans T2, m1.trans m2, g2.trans g1, l2.trans l1,
    c2.trans c1, st2.trans st1, Proofs.ModelProperties.Preceq_trans F1 F2⟩

omit [Inhabited V] in
/-- `Protocol.on_goldfish_vote_checked` satisfies `Keeps`. -/
theorem keeps_on_goldfish_vote_checked (P : Spec.Provisional V)
    (st : Spec.Store V) (u : Spec.GoldfishVote V) :
    Keeps st (Spec.Protocol.on_goldfish_vote_checked P st u) := by
  obtain ⟨gv, tv, he⟩ := on_goldfish_vote_checked_frame P st u
  rw [he]
  exact Keeps.refl st

omit [Fintype V] [Inhabited V] in
/-- `Protocol.admit_attestation` satisfies `Keeps`. -/
theorem keeps_admit_attestation (C : Spec.Config) (st : Spec.Store V)
    (a : Spec.Attestation V) :
    Keeps st (Spec.Protocol.admit_attestation C st a) := by
  obtain ⟨at', ts, he⟩ := admit_attestation_frame C st a
  rw [he]
  exact Keeps.refl st

omit [Fintype V] [Inhabited V] in
/-- `Protocol.admit_attestations` satisfies `Keeps`. -/
theorem keeps_admit_attestations (C : Spec.Config) (st : Spec.Store V)
    (rows : List (Spec.Attestation V)) :
    Keeps st (Spec.Protocol.admit_attestations C st rows) := by
  obtain ⟨at', ts, he⟩ := admit_attestations_frame C st rows
  rw [he]
  exact Keeps.refl st

omit [Fintype V] [Inhabited V] in
/-- `Protocol.update_finality` satisfies `Keeps`. -/
theorem keeps_update_finality (st : Spec.Store V) (B : Spec.Block V) :
    Keeps st (Spec.Protocol.update_finality st B) := by
  obtain ⟨hm, J, hj, F, he, hle, hF⟩ := update_finality_frame st B
  rw [he]
  exact ⟨rfl, rfl, subset_refl _, hle, rfl, rfl, rfl, rfl, hF⟩

/-- The store `b` has the clock, the slot, the attestations and the SG vote stamps of `a`. -/
def KeepsAtt (a b : Spec.Store V) : Prop :=
  b.t = a.t ∧ b.s = a.s ∧ b.attestations = a.attestations ∧
    b.timestamp_sg_vote = a.timestamp_sg_vote

omit [Inhabited V] in
/-- Admitting a list of Goldfish votes one by one satisfies `Keeps` and `KeepsAtt`. -/
theorem gf_votes_fold_keeps (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (x : Spec.Store V) :
    Keeps x (votes.foldl (fun b a => Spec.Protocol.on_goldfish_vote_checked P b a) x) ∧
      KeepsAtt x
        (votes.foldl (fun b a => Spec.Protocol.on_goldfish_vote_checked P b a) x) := by
  obtain ⟨gv, tv, he⟩ := gf_votes_fold_frame P votes x
  rw [he]
  exact ⟨Keeps.refl x, rfl, rfl, rfl, rfl⟩

omit [Fintype V] [Inhabited V] in
/-- `Protocol.update_finality` satisfies `KeepsAtt`. -/
theorem keepsAtt_update_finality (st : Spec.Store V) (B : Spec.Block V) :
    KeepsAtt st (Spec.Protocol.update_finality st B) := by
  obtain ⟨hm, J, hj, F, he, -, -⟩ := update_finality_frame st B
  rw [he]
  exact ⟨rfl, rfl, rfl, rfl⟩

omit [Inhabited V] in
/-- `Handlers.blockCore` satisfies `Keeps` and `KeepsAtt`, and its tree holds the block `B`. -/
theorem blockCore_keeps (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    Keeps st (Handlers.blockCore C P st B) ∧ KeepsAtt st (Handlers.blockCore C P st B) ∧
      B ∈ (Handlers.blockCore C P st B).T := by
  simp only [Handlers.blockCore, Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  refine ⟨Keeps.trans ?_ (Keeps.trans (gf_votes_fold_keeps P _ _).1 (keeps_update_finality _ B)),
    ?_, (Keeps.trans (gf_votes_fold_keeps P _ _).1 (keeps_update_finality _ B)).2.2.1 ?_⟩
  · exact ⟨rfl, rfl, Finset.subset_union_left, le_refl _, rfl, rfl, rfl, rfl,
      Proofs.ModelProperties.Preceq_self _⟩
  · obtain ⟨a1, a2, a3, a4⟩ := (gf_votes_fold_keeps P B.gf_votes _).2
    obtain ⟨b1, b2, b3, b4⟩ := keepsAtt_update_finality
      (B.gf_votes.foldl (fun b a => Spec.Protocol.on_goldfish_vote_checked P b a) _) B
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

omit [Inhabited V] in
/-- `Handlers.admitBlockCore` satisfies `Keeps` and `KeepsAtt`. -/
theorem admitBlockCore_keeps (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    Keeps st (Handlers.admitBlockCore C P st B) ∧
      KeepsAtt st (Handlers.admitBlockCore C P st B) := by
  unfold Handlers.admitBlockCore
  split
  · exact ⟨(blockCore_keeps C P st B).1, (blockCore_keeps C P st B).2.1⟩
  · exact ⟨Keeps.refl st, rfl, rfl, rfl, rfl⟩

omit [Inhabited V] in
/-- `Protocol.on_block` satisfies `Keeps`. -/
theorem keeps_on_block (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    Keeps st (Spec.Protocol.on_block C P st B) := by
  rw [Handlers.on_block_eq]
  split
  · exact (admitBlockCore_keeps C P st B).1.trans (keeps_admit_attestations C _ _)
  · exact Keeps.refl st

omit [Inhabited V] in
/-- The member `receipt_process` satisfies `Keeps`, whatever the object. -/
theorem keeps_receipt_process (S : Setup V) (st : Spec.Store V) (o : NamedObject V) :
    Keeps st (Member.receipt_process S st o) := by
  cases o with
  | block B => exact keeps_on_block _ _ _ _
  | gfVote u => exact keeps_on_goldfish_vote_checked _ _ _
  | attest a => exact keeps_admit_attestation _ _ _

omit [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.admit_attestation` keeps the saved grades. -/
theorem admit_attestation_saved_grades (C : Spec.Config) (st : Spec.Store V)
    (row : Spec.Attestation V) :
    (Spec.Protocol.admit_attestation C st row).saved_grades = st.saved_grades :=
  (keeps_admit_attestation C st row).2.2.2.2.1

omit [Inhabited V] in
/-- The spec's `Protocol.on_goldfish_vote_checked` keeps the saved grades. -/
theorem on_goldfish_vote_checked_saved_grades (P : Spec.Provisional V)
    (st : Spec.Store V) (vote : Spec.GoldfishVote V) :
    (Spec.Protocol.on_goldfish_vote_checked P st vote).saved_grades =
      st.saved_grades :=
  (keeps_on_goldfish_vote_checked P st vote).2.2.2.2.1

omit [Inhabited V] in
/-- The spec's `Protocol.on_block` keeps the saved grades. -/
theorem on_block_saved_grades (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).saved_grades = st.saved_grades :=
  (keeps_on_block C P st B).2.2.2.2.1

omit [Inhabited V] in
/-- `Protocol.block_admissible` refuses a block the tree already holds. -/
theorem block_admissible_of_mem (C : Spec.Config) (P : Spec.Provisional V)
    {st : Spec.Store V} {B : Spec.Block V} (hB : B ∈ st.T) :
    Spec.Protocol.block_admissible C P st B = false := by
  simp [Spec.Protocol.block_admissible, Id.run, hB, pure]

omit [Inhabited V] in
/-- `Protocol.block_admissible` refuses a block whose parent the tree does not hold. -/
theorem block_admissible_of_parent_not_mem (C : Spec.Config)
    (P : Spec.Provisional V) {st : Spec.Store V}
    {B : Spec.Block V} (hB : B.parent ∉ st.T) :
    Spec.Protocol.block_admissible C P st B = false := by
  simp [Spec.Protocol.block_admissible, Id.run, hB, pure]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `Spec.Block.toSpecNamed` of a named block's parent is the parent of its
    `Spec.Block.toSpecNamed`. -/
theorem toSpecNamed_parent (B : NamedBlock V) :
    (Spec.Block.toSpecNamed B).parent = Spec.Block.toSpecNamed B.parent := by
  cases B <;> simp [Spec.Block.toSpecNamed, Spec.Block.parent, NamedBlock.parent]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The attestations of `Spec.Block.toSpecNamed B` are those of `B` mapped by
    `Spec.Attestation.toSpecNamed`. -/
theorem toSpecNamed_attestations (B : NamedBlock V) :
    (Spec.Block.toSpecNamed B).attestations =
      B.attestations.map Spec.Attestation.toSpecNamed := by
  cases B <;> simp [Spec.Block.toSpecNamed, Spec.Block.attestations,
    NamedBlock.attestations]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A named block is among the bodies of a store exactly when its `Spec.Block.toSpecNamed` is in the
    store's tree. -/
theorem mem_bodies_iff (st : Spec.Store V) (B : NamedBlock V) :
    B ∈ Member.bodies st ↔ Spec.Block.toSpecNamed B ∈ st.T := by
  unfold Member.bodies
  rw [Finset.mem_map]
  constructor
  · rintro ⟨B', hB', rfl⟩
    simpa using hB'
  · intro h
    exact ⟨_, h, by simp⟩

omit [Inhabited V] in
/-- The member `receipt_process` keeps the saved grades, whatever the object. -/
theorem receipt_process_saved_grades (S : Setup V) (st : Spec.Store V)
    (o : NamedObject V) :
    (Member.receipt_process S st o).saved_grades = st.saved_grades :=
  (keeps_receipt_process S st o).2.2.2.2.1

/-- At `Model.specDraftBase`, the receipt of `o` by `n` returns exactly `receiveNamedObject S n o`. -/
theorem process_returns_iff (S : Setup V) (n n' : Spec.NodeState V)
    (o : NamedObject V) :
    (Model.specDraftBase (V := V)).process S n o ⇢ n' ↔ n' = receiveNamedObject S n o :=
  returns_pure _ _

omit [Inhabited V] in
/-- `receiveNamedObject S n o` is the member `receipt_process` on the store, followed by
    `make_grades_compatible_with_finalized`, the rest of the node state kept. -/
theorem receiveNamedObject_eq (S : Setup V) (n : Spec.NodeState V)
    (o : NamedObject V) :
    receiveNamedObject S n o =
      { n with st := Spec.make_grades_compatible_with_finalized (Member.receipt_process S n.st o) } := by
  cases o <;> rfl

omit [Inhabited V] in
/-- The member `derive_named`, mapped by `toProof`, is `Protocol.derive_named`. -/
theorem toProof_derive_named (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V) :
    (Member.derive_named E cfg B).toProof = Protocol.derive_named E cfg B := by
  induction B with
  | genesis =>
    simp only [Member.derive_named, Protocol.derive_named]
    exact toProof_cs_initial.symm
  | node p s r gv gs ats pr ih =>
    simp only [Member.derive_named, Protocol.derive_named, Member.named_transition]
    rw [← ih]
    have h := toProof_named_transition E unreadHealConfig cfg (Member.derive_named E cfg p)
      (Spec.Block.toSpecNamed (.node p s r gv gs ats pr))
    rw [Spec.Block.toProofNamed_toSpecNamed] at h
    rw [h]

omit [Inhabited V] in
/-- The image of the member `initial` is `NamedNode.initial`. -/
theorem toProof_initial (S : Setup V) (v : V) :
    (Member.initial S v).toProof = NamedNode.initial := by
  have hrec : (Spec.SigningHistory.initial).toProof = Protocol.NamedRecord.initial := by
    simp only [Spec.SigningHistory.toProof, Protocol.NamedRecord.initial,
      Protocol.Record.initial, Spec.SigningHistory.initial]
    rfl
  have hcache : (Spec.Protocol.initial_saved_grades : Spec.SavedGrades V).toProof =
      Protocol.initialCache := by
    simp only [Protocol.initialCache, Spec.Protocol.initial_saved_grades]
    unfold Protocol.emptyFrame Protocol.pendingFrame
    rfl
  simp only [NamedNode.initial, toProof_ns_initial, ← hrec, ← hcache]
  rfl

/-- The member `initial` of `Model.vocabulary` is the image of that of `Model.specDraftBase`. -/
theorem vocabulary_initial (S : Setup V) (v : V) :
    (Model.vocabulary (V := V)).initial S v = ((Model.specDraftBase (V := V)).initial S v).toProof :=
  (toProof_initial S v).symm

/-! ## The node's receipt of an object -/

/-- The field `process_record_eq` of `NodeFacts` at `Model.specDraftBase`: every node state `n'`
    that `n`'s receipt of the object `o` can return has the signing record of `n`. -/
theorem specDraftBase_process_record_eq : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n'.record = n.record := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  rfl

/-- The field `process_record_eq` of `NodeFacts` at `Model.specDraft`: every node state `n'` that
    `n`'s receipt of the object `o` can return has the signing record of `n`. -/
theorem specDraft_process_record_eq : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.record = n.record :=
  fun S n o n' hn' => specDraftBase_process_record_eq S n.val o n'.val hn'

omit [Inhabited V] in
/-- If the member `receipt_process` keeps the store and the saved grades are already clipped at the
    finalized block, the receipt of `o` keeps the node state. -/
theorem process_node_of_store_id_aux (S : Setup V) (n : Spec.NodeState V)
    (o : NamedObject V) (hst : Member.receipt_process S n.st o = n.st)
    (hcache : Spec.Protocol.make_saved_grades_compatible_with n.st.F n.st.saved_grades =
      n.st.saved_grades) :
    receiveNamedObject S n o = n := by
  rw [receiveNamedObject_eq, hst]
  cases n with
  | mk v st sh aw =>
    simp only [Spec.make_grades_compatible_with_finalized, Id.run]
    simp only at hcache
    rw [hcache]
    rfl

/-- The field `namedNodeProcess_setupWithGST` of `NodeFacts` at `Model.specDraft`: a node's
    processing of a delivered object is the same at the setup `S` and at `S` with its GST replaced
    by `g`. -/
theorem specDraft_namedNodeProcess_setupWithGST : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (g : ℤ) (hg : 0 ≤ g) (n : (Model.specDraft (V := V)).N) (o : DecoupledConsensusModel.Execution.NamedObject V), (Model.specDraft (V := V)).process (DecoupledConsensusModel.Sts.setupWithGST S g hg) n o = (Model.specDraft (V := V)).process S n o := by
  intro S g hg n o
  rfl

/-! ## The member `receipt_process` -/

/-- The field `process_block` of `NodeFacts` at `Model.specDraft`: processing the block `B` at the
    store `st` gives the store the block handler `on_block_with` returns, admitting the attestations
    `B` includes. -/
theorem specDraft_process_block : ∀ (S : Setup V) (st : (Model.specDraft (V := V)).NS) (B : NamedBlock V),
    (Model.specDraft (V := V)).receipt_process S st (.block B) = (Model.specDraft (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B := by
  intro S st B
  rfl

/-- The field `process_attest` of `NodeFacts` at `Model.specDraft`: processing the attestation `a`
    at the store `st` gives the store the row admission `admit_row` returns. -/
theorem specDraft_process_attest : ∀ (S : Setup V) (st : (Model.specDraft (V := V)).NS) (a : NamedAttestation V),
    (Model.specDraft (V := V)).receipt_process S st (.attest a) = (Model.specDraft (V := V)).admit_row S.hc st a := by
  intro S st a
  rfl

/-- The field `process_gfVote` of `NodeFacts` at `Model.specDraft`: processing the Goldfish vote `u`
    at the store `st` replaces `st`'s store part by the one the checked vote handler returns and
    keeps the rest of `st`. -/
theorem specDraft_process_gfVote : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (st : (Model.specDraft (V := V)).NS) (u : DecoupledConsensusModel.GoldfishVote V), (Model.specDraft (V := V)).receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u) = (Model.specDraft (V := V)).ns_with_core st ((Model.specDraft (V := V)).on_goldfish_vote_checked S.E st.core u) := by
  intro S st u
  rfl

/-- The field `process_gfVote_of_mem_pool` of `NodeFacts` at `Model.specDraftBase`: delivering a
    Goldfish vote that the store part of `st` already holds for that vote's slot leaves `st` as it
    was. -/
theorem specDraftBase_process_gfVote_of_mem_pool : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (st : (Model.specDraftBase (V := V)).NS) (u : DecoupledConsensusModel.GoldfishVote V), u ∈ st.core.pool u.slot → (Model.specDraftBase (V := V)).receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u) = st := by
  intro S st u hu
  have hu1 : u ∈ (st.pool u.slot).map Spec.GoldfishVote.toProofEmb := hu
  rw [Finset.mem_map] at hu1
  obtain ⟨w, hw, rfl⟩ := hu1
  have hw' : w ∈ st.gf_votes w.slot := by
    have h := hw
    simp only [Spec.Store.pool, List.mem_toFinset] at h
    exact h
  show Spec.Protocol.on_goldfish_vote_checked _ st
    (Spec.GoldfishVote.toSpec (Spec.GoldfishVote.toProofEmb w)) = st
  rw [Spec.GoldfishVote.coe_toProofEmb, Spec.GoldfishVote.toSpec_toProof]
  simp only [Spec.Protocol.on_goldfish_vote_checked,
    Spec.Protocol.on_goldfish_vote, Id.run, pure]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exfalso
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h2
    exact h2.2 hw'
  · rfl

/-- The field `process_gfVote_of_mem_pool` of `NodeFacts` at `Model.specDraft`: delivering a
    Goldfish vote that the store part of `st` already holds for that vote's slot leaves `st` as it
    was. -/
theorem specDraft_process_gfVote_of_mem_pool : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (st : (Model.specDraft (V := V)).NS) (u : DecoupledConsensusModel.GoldfishVote V), u ∈ st.core.pool u.slot → (Model.specDraft (V := V)).receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u) = st :=
by
  intro S st u hu
  by_cases hr : objectRootHeldByOther st.val.T (NamedObject.gfVote u)
  · exact OkMember.receipt_process_of_held hr
  · apply Subtype.ext
    show (OkMember.receipt_process S st (NamedObject.gfVote u)).val = st.val
    rw [OkMember.receipt_process_val_of_not_held hr]
    exact specDraftBase_process_gfVote_of_mem_pool S st.val u hu

/-- The field `process_attest_of_mem_rows` of `NodeFacts` at `Model.specDraftBase`: delivering an
    attestation that `st` already holds among its named rows for that round leaves `st` as it was. -/
theorem specDraftBase_process_attest_of_mem_rows : ∀ (S : Setup V) (st : (Model.specDraftBase (V := V)).NS) (a : NamedAttestation V)
    (hPool : ∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase)
    (ha : a ∈ st.sg_rows a.round), (Model.specDraftBase (V := V)).receipt_process S st (NamedObject.attest a) = st := by
  intro S st a _ ha
  have ha1 : a ∈ (st.attestations a.round).map Spec.Attestation.toProofNamed := ha
  rw [List.mem_map] at ha1
  obtain ⟨w, hw, rfl⟩ := ha1
  show Spec.Protocol.admit_attestation _ st
    (Spec.Attestation.toSpecNamed w.toProofNamed) = st
  rw [Spec.Attestation.toSpecNamed_toProofNamed]
  have hw' : w.round = w.toProofNamed.round := rfl
  rw [← hw'] at hw
  have hmem : w.confirmed ∈ Spec.Protocol.round_votes st w := by
    unfold Spec.Protocol.round_votes
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw, rfl⟩, rfl⟩
  simp only [Spec.Protocol.admit_attestation, Id.run, pure]
  split_ifs with h1
  · exfalso
    simp [Spec.Protocol.attestation_admissible, Id.run, hmem] at h1
  · rfl

/-- The field `process_attest_of_mem_rows` of `NodeFacts` at `Model.specDraft`: delivering an
    attestation that `st` already holds among its named rows for that round leaves `st` as it was. -/
theorem specDraft_process_attest_of_mem_rows : ∀ (S : Setup V) (st : (Model.specDraft (V := V)).NS) (a : NamedAttestation V)
    (hPool : ∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase)
    (ha : a ∈ st.sg_rows a.round), (Model.specDraft (V := V)).receipt_process S st (NamedObject.attest a) = st :=
by
  intro S st a hPool ha
  by_cases hr : objectRootHeldByOther st.val.T (NamedObject.attest a)
  · exact OkMember.receipt_process_of_held hr
  · apply Subtype.ext
    show (OkMember.receipt_process S st (NamedObject.attest a)).val = st.val
    rw [OkMember.receipt_process_val_of_not_held hr]
    exact specDraftBase_process_attest_of_mem_rows S st.val a hPool ha

/-- The field `process_block_of_mem_bodies` of `NodeFacts` at `Model.specDraftBase`: delivering a
    block that `st` already holds among its bodies leaves `st` as it was. -/
theorem specDraftBase_process_block_of_mem_bodies : ∀ (S : Setup V) (st : (Model.specDraftBase (V := V)).NS) (B : NamedBlock V)
    (hT : st.core.T = st.bodies.image NamedBlock.erase) (hB : B ∈ st.bodies),
    (Model.specDraftBase (V := V)).receipt_process S st (NamedObject.block B) = st := by
  intro S st B _ hB
  have hB' := (mem_bodies_iff st B).mp hB
  show Spec.Protocol.on_block _ _ st (Spec.Block.toSpecNamed B) = st
  rw [Handlers.on_block_eq, block_admissible_of_mem _ _ hB']
  rfl

/-- The field `process_block_of_mem_bodies` of `NodeFacts` at `Model.specDraft`: delivering a block
    that `st` already holds among its bodies leaves `st` as it was. -/
theorem specDraft_process_block_of_mem_bodies : ∀ (S : Setup V) (st : (Model.specDraft (V := V)).NS) (B : NamedBlock V)
    (hT : st.core.T = st.bodies.image NamedBlock.erase) (hB : B ∈ st.bodies),
    (Model.specDraft (V := V)).receipt_process S st (NamedObject.block B) = st :=
by
  intro S st B hT hB
  by_cases hr : objectRootHeldByOther st.val.T (NamedObject.block B)
  · exact OkMember.receipt_process_of_held hr
  · apply Subtype.ext
    show (OkMember.receipt_process S st (NamedObject.block B)).val = st.val
    rw [OkMember.receipt_process_val_of_not_held hr]
    exact specDraftBase_process_block_of_mem_bodies S st.val B hT hB

/-! ## The core call, the node's parts and the initial node state -/

/-- The field `postCore_clock` of `NodeFacts` at `Model.specDraftBase`: the core call on `B` keeps
    the clock `t` and the slot `s` of `before`'s store part. -/
theorem specDraftBase_postCore_clock : ∀ (S : Setup V) (before : (Model.specDraftBase (V := V)).NS) (B : NamedBlock V),
    ((Model.specDraftBase (V := V)).postCore S before B).core.t = before.core.t ∧
      ((Model.specDraftBase (V := V)).postCore S before B).core.s = before.core.s := by
  intro S before B
  have h := (admitBlockCore_keeps (Spec.Config.toSpec S.E S.hc S.cfg)
    (Spec.Provisional.toSpec S.E) before (Spec.Block.toSpecNamed B)).2
  exact ⟨h.1, h.2.1⟩

/-- The field `postCore_clock` of `NodeFacts` at `Model.specDraft`: the core call on `B` keeps the
    clock `t` and the slot `s` of `before`'s store part. -/
theorem specDraft_postCore_clock : ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V),
    ((Model.specDraft (V := V)).postCore S before B).core.t = before.core.t ∧
      ((Model.specDraft (V := V)).postCore S before B).core.s = before.core.s :=
by
  intro S before B
  by_cases hr : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · have e : (Model.specDraft (V := V)).postCore S before B = before := OkMember.postCore_of_held hr
    rw [e]
    exact ⟨rfl, rfl⟩
  · have e : ((Model.specDraft (V := V)).postCore S before B).val = (Model.specDraftBase (V := V)).postCore S before.val B :=
      OkMember.postCore_val_of_not_held hr
    have hb := specDraftBase_postCore_clock S before.val B
    rw [← e] at hb
    exact hb

/-- The field `postCore_eq_process_block_core` of `NodeFacts` at `Model.specDraft`: the core call on
    `B` from `before` is the member `ns_process_block_core` at the setup's environment, healing
    configuration and height configuration. -/
theorem specDraft_postCore_eq_process_block_core : ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V),
    (Model.specDraft (V := V)).postCore S before B = (Model.specDraft (V := V)).ns_process_block_core S.E S.hc S.cfg before B := by
  intro S before B
  rfl

/-- The field `postCore_of_parent_not_mem` of `NodeFacts` at `Model.specDraftBase`: if `before` does
    not hold the parent body of `B`, the core call on `B` returns `before`. -/
theorem specDraftBase_postCore_of_parent_not_mem : ∀ (S : Setup V) {before : (Model.specDraftBase (V := V)).NS} {B : NamedBlock V}
    (h : B.parent ∉ before.bodies), (Model.specDraftBase (V := V)).postCore S before B = before := by
  intro S before B h
  have h' : (Spec.Block.toSpecNamed B).parent ∉ before.T := by
    rw [toSpecNamed_parent]
    exact fun hm => h ((mem_bodies_iff before B.parent).mpr hm)
  show Handlers.admitBlockCore _ _ before (Spec.Block.toSpecNamed B) = before
  unfold Handlers.admitBlockCore
  rw [block_admissible_of_parent_not_mem _ _ h']
  rfl

/-- The field `postCore_of_parent_not_mem` of `NodeFacts` at `Model.specDraft`: if `before` does not
    hold the parent body of `B`, the core call on `B` returns `before`. -/
theorem specDraft_postCore_of_parent_not_mem : ∀ (S : Setup V) {before : (Model.specDraft (V := V)).NS} {B : NamedBlock V}
    (h : B.parent ∉ before.bodies), (Model.specDraft (V := V)).postCore S before B = before :=
by
  intro S before B h
  by_cases hr : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · exact OkMember.postCore_of_held hr
  · apply Subtype.ext
    have e : ((Model.specDraft (V := V)).postCore S before B).val = (Model.specDraftBase (V := V)).postCore S before.val B :=
      OkMember.postCore_val_of_not_held hr
    rw [e]
    exact specDraftBase_postCore_of_parent_not_mem S (before := before.val) (B := B) h

/-- The field `postCore_sg_rows` of `NodeFacts` at `Model.specDraftBase`: the core call on `B` keeps
    the named SG rows of `before`. -/
theorem specDraftBase_postCore_sg_rows : ∀ (S : Setup V) (before : (Model.specDraftBase (V := V)).NS) (B : NamedBlock V),
    ((Model.specDraftBase (V := V)).postCore S before B).sg_rows = before.sg_rows := by
  intro S before B
  have h := (admitBlockCore_keeps (Spec.Config.toSpec S.E S.hc S.cfg)
    (Spec.Provisional.toSpec S.E) before (Spec.Block.toSpecNamed B)).2.2.2.1
  funext r
  show ((Handlers.admitBlockCore _ _ before _).attestations r).map
      Spec.Attestation.toProofNamed =
    (before.attestations r).map Spec.Attestation.toProofNamed
  rw [h]

/-- The field `postCore_sg_rows` of `NodeFacts` at `Model.specDraft`: the core call on `B` keeps the
    named SG rows of `before`. -/
theorem specDraft_postCore_sg_rows : ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V),
    ((Model.specDraft (V := V)).postCore S before B).sg_rows = before.sg_rows :=
by
  intro S before B
  by_cases hr : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · have e : (Model.specDraft (V := V)).postCore S before B = before := OkMember.postCore_of_held hr
    rw [e]
  · have e : ((Model.specDraft (V := V)).postCore S before B).val = (Model.specDraftBase (V := V)).postCore S before.val B :=
      OkMember.postCore_val_of_not_held hr
    have hb := specDraftBase_postCore_sg_rows S before.val B
    rw [← e] at hb
    exact hb

/-- The field `postCore_timestamp_sg_vote` of `NodeFacts` at `Model.specDraftBase`: the core call on
    `B` keeps the SG vote stamps of `before`. -/
theorem specDraftBase_postCore_timestamp_sg_vote : ∀ (S : Setup V) (before : (Model.specDraftBase (V := V)).NS) (B : NamedBlock V),
    ((Model.specDraftBase (V := V)).postCore S before B).core.timestamp_sg_vote = before.core.timestamp_sg_vote := by
  intro S before B
  have h := (admitBlockCore_keeps (Spec.Config.toSpec S.E S.hc S.cfg)
    (Spec.Provisional.toSpec S.E) before (Spec.Block.toSpecNamed B)).2.2.2.2
  funext u
  show (Handlers.admitBlockCore _ _ before _).timestamp_sg_vote
      (Spec.Protocol.SGVote.toSpec u) =
    before.timestamp_sg_vote (Spec.Protocol.SGVote.toSpec u)
  rw [h]

/-- The field `postCore_timestamp_sg_vote` of `NodeFacts` at `Model.specDraft`: the core call on `B`
    keeps the SG vote stamps of `before`. -/
theorem specDraft_postCore_timestamp_sg_vote : ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V),
    ((Model.specDraft (V := V)).postCore S before B).core.timestamp_sg_vote = before.core.timestamp_sg_vote :=
by
  intro S before B
  by_cases hr : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · have e : (Model.specDraft (V := V)).postCore S before B = before := OkMember.postCore_of_held hr
    rw [e]
  · have e : ((Model.specDraft (V := V)).postCore S before B).val = (Model.specDraftBase (V := V)).postCore S before.val B :=
      OkMember.postCore_val_of_not_held hr
    have hb := specDraftBase_postCore_timestamp_sg_vote S before.val B
    rw [← e] at hb
    exact hb

/-- The field `on_block_with_eq_postCore_of_not_new` of `NodeFacts` at `Model.specDraftBase`: unless
    `B` is not among the bodies of `before` and is among the bodies after the core call on `B`, the
    block handler `on_block_with` on `B` at `before` returns the store after the core call. -/
theorem specDraftBase_on_block_with_eq_postCore_of_not_new : ∀ (S : Setup V) (before : (Model.specDraftBase (V := V)).NS) (B : NamedBlock V)
    (h : ¬ (B ∉ before.bodies ∧ B ∈ ((Model.specDraftBase (V := V)).postCore S before B).bodies)),
    (Model.specDraftBase (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B = (Model.specDraftBase (V := V)).postCore S before B := by
  intro S before B h
  show Spec.Protocol.on_block _ _ before (Spec.Block.toSpecNamed B) =
    Handlers.admitBlockCore _ _ before (Spec.Block.toSpecNamed B)
  rw [Handlers.on_block_eq]
  unfold Handlers.admitBlockCore
  split
  · rename_i hadm
    exfalso
    apply h
    refine ⟨fun hm => ?_, ?_⟩
    · rw [block_admissible_of_mem _ _ ((mem_bodies_iff before B).mp hm)] at hadm
      exact Bool.false_ne_true hadm
    · show B ∈ Member.bodies (Handlers.admitBlockCore _ _ before _)
      rw [mem_bodies_iff]
      unfold Handlers.admitBlockCore
      rw [if_pos hadm]
      exact (blockCore_keeps _ _ before _).2.2
  · rfl

/-- The field `on_block_with_eq_postCore_of_not_new` of `NodeFacts` at `Model.specDraft`: unless `B`
    is not among the bodies of `before` and is among the bodies after the core call on `B`, the
    block handler `on_block_with` on `B` at `before` returns the store after the core call. -/
theorem specDraft_on_block_with_eq_postCore_of_not_new : ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V)
    (h : ¬ (B ∉ before.bodies ∧ B ∈ ((Model.specDraft (V := V)).postCore S before B).bodies)),
    (Model.specDraft (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B = (Model.specDraft (V := V)).postCore S before B :=
by
  intro S before B h
  by_cases hr : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · have e1 : (Model.specDraft (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B = before := OkMember.on_block_with_of_held hr
    have e2 : (Model.specDraft (V := V)).postCore S before B = before := OkMember.postCore_of_held hr
    rw [e1, e2]
  · have e1 : ((Model.specDraft (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B).val = (Model.specDraftBase (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before.val B := OkMember.on_block_with_val_of_not_held hr
    have e2 : ((Model.specDraft (V := V)).postCore S before B).val = (Model.specDraftBase (V := V)).postCore S before.val B :=
      OkMember.postCore_val_of_not_held hr
    apply Subtype.ext
    rw [e1, e2]
    refine specDraftBase_on_block_with_eq_postCore_of_not_new S before.val B ?_
    rw [← e2]
    exact h

/-- The field `on_block_with_eq_admit_rows_postCore` of `NodeFacts` at `Model.specDraftBase`: if `B`
    is not among the bodies of `before` and is among the bodies after the core call on `B`, the
    block handler `on_block_with` on `B` at `before` returns the store that admitting the
    attestations `B` includes, one by one, returns from the store after the core call. -/
theorem specDraftBase_on_block_with_eq_admit_rows_postCore : ∀ (S : Setup V) (before : (Model.specDraftBase (V := V)).NS) (B : NamedBlock V)
    (hnew : B ∉ before.bodies) (hheld : B ∈ ((Model.specDraftBase (V := V)).postCore S before B).bodies),
    (Model.specDraftBase (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B =
      (Model.specDraftBase (V := V)).admit_rows S.hc ((Model.specDraftBase (V := V)).postCore S before B) B.attestations := by
  intro S before B hnew hheld
  show Spec.Protocol.on_block _ _ before (Spec.Block.toSpecNamed B) =
    Spec.Protocol.admit_attestations _
      (Handlers.admitBlockCore _ _ before (Spec.Block.toSpecNamed B))
      (B.attestations.map Spec.Attestation.toSpecNamed)
  rw [Handlers.on_block_eq, ← toSpecNamed_attestations]
  split
  · rfl
  · rename_i hadm
    exfalso
    have hheld' : B ∈ Member.bodies (Handlers.admitBlockCore _ _ before _) := hheld
    unfold Handlers.admitBlockCore at hheld'
    rw [if_neg hadm] at hheld'
    exact hnew hheld'

/-- The field `on_block_with_eq_admit_rows_postCore` of `NodeFacts` at `Model.specDraft`: if `B` is
    not among the bodies of `before` and is among the bodies after the core call on `B`, the block
    handler `on_block_with` on `B` at `before` returns the store that admitting the attestations `B`
    includes, one by one, returns from the store after the core call. -/
theorem specDraft_on_block_with_eq_admit_rows_postCore : ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V)
    (hnew : B ∉ before.bodies) (hheld : B ∈ ((Model.specDraft (V := V)).postCore S before B).bodies),
    (Model.specDraft (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B =
      (Model.specDraft (V := V)).admit_rows S.hc ((Model.specDraft (V := V)).postCore S before B) B.attestations :=
by
  intro S before B hnew hheld
  by_cases hr : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · exfalso
    have e2 : (Model.specDraft (V := V)).postCore S before B = before := OkMember.postCore_of_held hr
    rw [e2] at hheld
    exact hnew hheld
  · have e1 : ((Model.specDraft (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before B).val = (Model.specDraftBase (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg before.val B := OkMember.on_block_with_val_of_not_held hr
    have e2 : ((Model.specDraft (V := V)).postCore S before B).val = (Model.specDraftBase (V := V)).postCore S before.val B :=
      OkMember.postCore_val_of_not_held hr
    have e3 : ((Model.specDraft (V := V)).admit_rows S.hc ((Model.specDraft (V := V)).postCore S before B) B.attestations).val =
        (Model.specDraftBase (V := V)).admit_rows S.hc ((Model.specDraft (V := V)).postCore S before B).val B.attestations := rfl
    apply Subtype.ext
    rw [e1, e3, e2]
    refine specDraftBase_on_block_with_eq_admit_rows_postCore S before.val B hnew ?_
    rw [← e2]
    exact hheld

/-- The field `process_h_max_mono` of `NodeFacts` at `Model.specDraftBase`: every node state `n'`
    that `n`'s receipt of `o` can return has an `h_max` at least `n`'s. -/
theorem specDraftBase_process_h_max_mono : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n.st.core.h_max ≤ n'.st.core.h_max := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  exact (keeps_receipt_process S n.st o).2.2.2.1

/-- The field `process_h_max_mono` of `NodeFacts` at `Model.specDraft`: every node state `n'` that
    `n`'s receipt of `o` can return has an `h_max` at least `n`'s. -/
theorem specDraft_process_h_max_mono : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n.st.core.h_max ≤ n'.st.core.h_max :=
  fun S n o n' hn' => specDraftBase_process_h_max_mono S n.val o n'.val hn'

/-- The field `node_process_F` of `NodeFacts` at `Model.specDraftBase`: for every node state `n'`
    that `n`'s receipt of `o` can return, `n`'s finalized block is an ancestor of, or equal to,
    `n'`'s. -/
theorem specDraftBase_node_process_F : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), Block.Preceq n.st.core.F n'.st.core.F := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  exact (keeps_receipt_process S n.st o).2.2.2.2.2.2.2.2

/-- The field `node_process_F` of `NodeFacts` at `Model.specDraft`: for every node state `n'` that
    `n`'s receipt of `o` can return, `n`'s finalized block is an ancestor of, or equal to, `n'`'s. -/
theorem specDraft_node_process_F : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), Block.Preceq n.st.core.F n'.st.core.F :=
  fun S n o n' hn' => specDraftBase_node_process_F S n.val o n'.val hn'

/-- The field `process_cache_round` of `NodeFacts` at `Model.specDraftBase`: every node state `n'`
    that `n`'s receipt of `o` can return has a grade cache of the round of `n`'s. -/
theorem specDraftBase_process_cache_round : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n'.cache.round = n.cache.round := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  show (Member.receipt_process S n.st o).saved_grades.round = n.st.saved_grades.round
  rw [receipt_process_saved_grades]

/-- The field `process_cache_round` of `NodeFacts` at `Model.specDraft`: every node state `n'` that
    `n`'s receipt of `o` can return has a grade cache of the round of `n`'s. -/
theorem specDraft_process_cache_round : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.cache.round = n.cache.round :=
  fun S n o n' hn' => specDraftBase_process_cache_round S n.val o n'.val hn'

/-- The field `process_clock` of `NodeFacts` at `Model.specDraftBase`: every node state `n'` that
    `n`'s receipt of `o` can return has the clock `t` and the slot `s` of `n`'s store part. -/
theorem specDraftBase_process_clock : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n'.st.core.t = n.st.core.t ∧ n'.st.core.s = n.st.core.s := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  exact ⟨(keeps_receipt_process S n.st o).1, (keeps_receipt_process S n.st o).2.1⟩

/-- The field `process_clock` of `NodeFacts` at `Model.specDraft`: every node state `n'` that `n`'s
    receipt of `o` can return has the clock `t` and the slot `s` of `n`'s store part. -/
theorem specDraft_process_clock : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.st.core.t = n.st.core.t ∧ n'.st.core.s = n.st.core.s :=
  fun S n o n' hn' => specDraftBase_process_clock S n.val o n'.val hn'

/-- The field `node_process_latest` of `NodeFacts` at `Model.specDraftBase`: every node state `n'`
    that `n`'s receipt of `o` can return has the `latest_confirmed` of `n`'s store part. -/
theorem specDraftBase_node_process_latest : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n'.st.core.latest_confirmed = n.st.core.latest_confirmed := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  show (Member.receipt_process S n.st o).latest_confirmed.toProof = n.st.latest_confirmed.toProof
  rw [(keeps_receipt_process S n.st o).2.2.2.2.2.2.1]

/-- The field `node_process_latest` of `NodeFacts` at `Model.specDraft`: every node state `n'` that
    `n`'s receipt of `o` can return has the `latest_confirmed` of `n`'s store part. -/
theorem specDraft_node_process_latest : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.st.core.latest_confirmed = n.st.core.latest_confirmed :=
  fun S n o n' hn' => specDraftBase_node_process_latest S n.val o n'.val hn'

/-- The field `node_process_stable` of `NodeFacts` at `Model.specDraftBase`: every node state `n'`
    that `n`'s receipt of `o` can return has the `latest_stable` of `n`'s store part. -/
theorem specDraftBase_node_process_stable : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n'.st.core.latest_stable = n.st.core.latest_stable := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  show (Member.receipt_process S n.st o).latest_stable.toProof = n.st.latest_stable.toProof
  rw [(keeps_receipt_process S n.st o).2.2.2.2.2.2.2.1]

/-- The field `node_process_stable` of `NodeFacts` at `Model.specDraft`: every node state `n'` that
    `n`'s receipt of `o` can return has the `latest_stable` of `n`'s store part. -/
theorem specDraft_node_process_stable : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.st.core.latest_stable = n.st.core.latest_stable :=
  fun S n o n' hn' => specDraftBase_node_process_stable S n.val o n'.val hn'

/-- The field `process_record` of `NodeFacts` at `Model.specDraft`: every node state `n'` that `n`'s
    receipt of `o` can return has the signing record of `n`. -/
theorem specDraft_process_record : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.record = n.record := by
  exact specDraft_process_record_eq

/-- The field `mkNode_record` of `NodeFacts` at `Model.specDraft`: the signing record of
    `mkNode st rc c` is `rc`. -/
theorem specDraft_mkNode_record : ∀ (st : (Model.specDraft (V := V)).NS) (rc : (Model.specDraft (V := V)).NR) (c : (Model.specDraft (V := V)).Cache), ((Model.specDraft (V := V)).mkNode st rc c).record = rc := by
  intro st rc c
  rfl

/-- The field `mkNode_st` of `NodeFacts` at `Model.specDraft`: the named store of `mkNode st rc c`
    is `store_with_cache st c`. -/
theorem specDraft_mkNode_st : ∀ (st : (Model.specDraft (V := V)).NS) (rc : (Model.specDraft (V := V)).NR) (c : (Model.specDraft (V := V)).Cache), ((Model.specDraft (V := V)).mkNode st rc c).st = (Model.specDraft (V := V)).store_with_cache st c := by
  intro st rc c
  rfl

/-- The field `mkNode_cache` of `NodeFacts` at `Model.specDraft`: the cache of `mkNode st rc c` is
    `c`. -/
theorem specDraft_mkNode_cache : ∀ (st : (Model.specDraft (V := V)).NS) (rc : (Model.specDraft (V := V)).NR) (c : (Model.specDraft (V := V)).Cache), ((Model.specDraft (V := V)).mkNode st rc c).cache = c := by
  intro st rc c
  rfl

/-- The field `wake_st_record` of `NodeFacts` at `Model.specDraft`: a wake keeps the node's store
    and its signing record. -/
theorem specDraft_wake_st_record : ∀ n : (Model.specDraft (V := V)).N, ((Model.specDraft (V := V)).wake n).st = n.st ∧ ((Model.specDraft (V := V)).wake n).record = n.record := by
  intro n
  exact ⟨rfl, rfl⟩

/-- The field `gradeContract_sgVote` of `NodeFacts` at `Model.specDraft`: the SG vote of the
    contract built from any cache `c` is `currentSGVote`. -/
theorem specDraft_gradeContract_sgVote : ∀ (c : (Model.specDraft (V := V)).Cache), ((Model.specDraft (V := V)).gradeContract c).sgVote = (Model.specDraft (V := V)).currentSGVote := by
  intro c
  rfl

/-- The field `cache_clipped_initial` of `NodeFacts` at `Model.specDraft`: the grade cache of the
    initial node state, clipped at the finalized block of its store, is that cache. -/
theorem specDraft_cache_clipped_initial : ∀ (S : Setup V) (v : V),
    (Model.specDraft (V := V)).clipCache ((Model.specDraft (V := V)).initial S v).st.core.F ((Model.specDraft (V := V)).initial S v).cache = ((Model.specDraft (V := V)).initial S v).cache := by
  intro S v
  rfl

/-- The field `initial_cache_current_phase` of `NodeFacts` at `Model.specDraft`: for every phase
    `p`, the current frame of the initial node state's grade cache has the result `some none` for
    `p`. -/
theorem specDraft_initial_cache_current_phase : ∀ (S : Setup V) (v : V) (p : DecoupledConsensusModel.Protocol.Phase), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).initial S v).cache.current p = Option.some Option.none := by
  intro S v p
  cases p <;> rfl

/-- The field `initial_cache_round` of `NodeFacts` at `Model.specDraft`: the round of the initial
    node state's grade cache is `0`. -/
theorem specDraft_initial_cache_round : ∀ (S : Setup V) (v : V), ((Model.specDraft (V := V)).initial S v).cache.round = 0 := by
  intro S v
  rfl

/-- The field `initial_record_legacy_lock` of `NodeFacts` at `Model.specDraft`: the initial signing
    record holds no lock at any height. -/
theorem specDraft_initial_record_legacy_lock : ∀ (S : Setup V) (v : V) (H : Height), ((Model.specDraft (V := V)).initial S v).record.legacy.lock H = none := by
  intro S v H
  rfl

/-- The field `initial_record_legacy_target` of `NodeFacts` at `Model.specDraft`: the initial
    signing record records no target at any height. -/
theorem specDraft_initial_record_legacy_target : ∀ (S : Setup V) (v : V) (h : Height), ((Model.specDraft (V := V)).initial S v).record.legacy.target h = none := by
  intro S v h
  rfl

/-- The field `initial_record_legacy_timeout` of `NodeFacts` at `Model.specDraft`: the initial
    signing record records no timeout at any height. -/
theorem specDraft_initial_record_legacy_timeout : ∀ (S : Setup V) (v : V) (h : Height),
    ((Model.specDraft (V := V)).initial S v).record.legacy.timeout h = false := by
  intro S v h
  rfl

/-- The field `initial_record_lock` of `NodeFacts` at `Model.specDraft`: the initial signing record
    holds no lock at any height. -/
theorem specDraft_initial_record_lock : ∀ (S : Setup V) (v : V) (h : Height), ((Model.specDraft (V := V)).initial S v).record.legacy.lock h = none := by
  intro S v h
  rfl

/-- The field `initial_record_target` of `NodeFacts` at `Model.specDraft`: the initial signing
    record records no target at any height. -/
theorem specDraft_initial_record_target : ∀ (S : Setup V) (v : V) (h : Height), ((Model.specDraft (V := V)).initial S v).record.legacy.target h = none := by
  intro S v h
  rfl

/-- The field `initial_st` of `NodeFacts` at `Model.specDraft`: the store of the initial node state
    is `ns_initial`. -/
theorem specDraft_initial_st : ∀ (S : Setup V) (v : V), ((Model.specDraft (V := V)).initial S v).st = (Model.specDraft (V := V)).ns_initial := by
  intro S v
  rfl

/-- The field `initial_st_inclG2` of `NodeFacts` at `Model.specDraft`: the store of the initial node
    state is `ns_initial`. -/
theorem specDraft_initial_st_inclG2 : ∀ (S : Setup V) (v : V), ((Model.specDraft (V := V)).initial S v).st = ((Model.specDraft (V := V)).ns_initial : (Model.specDraft (V := V)).NS) := by
  intro S v
  rfl

/-- The field `initial_clock_eq_zero` of `NodeFacts` at `Model.specDraft`: the clock of the initial
    node state's store is `0`. -/
theorem specDraft_initial_clock_eq_zero : ∀ (S : Setup V) (v : V), ((Model.specDraft (V := V)).initial S v).st.core.t = 0 := by
  intro S v
  rfl

/-- The field `initial_body_eq_genesis` of `NodeFacts` at `Model.specDraft`: every body of the
    initial node state is genesis. -/
theorem specDraft_initial_body_eq_genesis : ∀ (S : Setup V) (v : V) {D : NamedBlock V} (hD : D ∈ ((Model.specDraft (V := V)).initial S v).st.bodies),
    D = NamedBlock.genesis := by
  intro S v D hD
  have hD' : D ∈ (Spec.Store.init : Spec.Store V).T.map
      Spec.Block.toProofNamedEmb := hD
  simp only [Spec.Store.init, Finset.map_singleton, Finset.mem_singleton,
    Spec.Block.coe_toProofNamedEmb] at hD'
  rw [hD']
  rfl

/-- The field `initial_timestamp_genesis` of `NodeFacts` at `Model.specDraftBase`: in the initial
    node state, genesis carries the stamp `⊥`. -/
theorem specDraftBase_initial_timestamp_genesis : ∀ (S : Setup V) (v : V), ((Model.specDraftBase (V := V)).initial S v).st.core.timestamp_block Block.genesis = some ⊥ := by
  intro S v
  have h := (Model.vocabulary_facts_node (V := V)).initial_timestamp_genesis S v
  rw [vocabulary_initial] at h
  exact h

/-- The field `initial_timestamp_genesis` of `NodeFacts` at `Model.specDraft`: in the initial node
    state, genesis carries the stamp `⊥`. -/
theorem specDraft_initial_timestamp_genesis : ∀ (S : Setup V) (v : V), ((Model.specDraft (V := V)).initial S v).st.core.timestamp_block Block.genesis = some ⊥ :=
  fun S v => specDraftBase_initial_timestamp_genesis S v

/-- The field `initial_cache_phaseResult_ne` of `NodeFacts` at `Model.specDraftBase`: no round's
    frame of the initial node state's grade cache has a phase result of the form `some (some root)`. -/
theorem specDraftBase_initial_cache_phaseResult_ne : ∀ (S : Setup V) (v : V) (r₁ : Round) (p : Protocol.Phase) (root : Block V),
    (Model.specDraftBase (V := V)).phaseResult ((Model.specDraftBase (V := V)).cacheAtRound ((Model.specDraftBase (V := V)).initial S v).cache r₁) p ≠ some (some root) := by
  intro S v r₁ p root
  have h := (Model.vocabulary_facts_node (V := V)).initial_cache_phaseResult_ne S v r₁ p root
  rw [vocabulary_initial] at h
  have e1 := toProof_phaseResult
    (Spec.Protocol.saved_round_grades ((Model.specDraftBase (V := V)).initial S v).st.saved_grades r₁)
    (Spec.Protocol.Phase.toSpec p)
  rw [Spec.Protocol.Phase.toProof_toSpec] at e1
  have e2 := toProof_cacheAtRound ((Model.specDraftBase (V := V)).initial S v).st.saved_grades r₁
  show (Spec.Protocol.phaseResult
    (Spec.Protocol.saved_round_grades ((Model.specDraftBase (V := V)).initial S v).st.saved_grades r₁)
      (Spec.Protocol.Phase.toSpec p)).toProof ≠ _
  rw [← e1, ← e2]
  exact h

/-- The field `initial_cache_phaseResult_ne` of `NodeFacts` at `Model.specDraft`: no round's frame
    of the initial node state's grade cache has a phase result of the form `some (some root)`. -/
theorem specDraft_initial_cache_phaseResult_ne : ∀ (S : Setup V) (v : V) (r₁ : Round) (p : Protocol.Phase) (root : Block V),
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).initial S v).cache r₁) p ≠ some (some root) :=
  fun S v r₁ p root => specDraftBase_initial_cache_phaseResult_ne S v r₁ p root

/-! ## The tick -/

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A `DRE` answer `a` lifted into `DREB` and bound to `f` is `f a`. -/
theorem liftM_ok_bind {α β : Type} (a : α) (f : α → Spec.DREB V β) :
    ((liftM (Except.ok a : DC.DRE α) : Spec.DREB V α) >>= f) = f a := rfl

omit [Inhabited V] in
/-- What a successful run of the spec's proposal duty does: it admits a block `B` with `on_block`
    and broadcasts it. -/
theorem propose_block_run {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {v : V} {st st' : Spec.Store V}
    {l l' : List (Spec.NamedObject V)}
    (h : (Spec.Protocol.propose_block C P X v st).run l = .ok (st', l')) :
    ∃ B : Spec.Block V, st' = Spec.Protocol.on_block C P st B ∧
      l' = l ++ [Spec.NamedObject.block B] := by
  unfold Spec.Protocol.propose_block at h
  cases hb : Spec.Protocol.build_proposal C X v st with
  | error e =>
    rw [hb] at h
    cases h
  | ok B =>
    rw [hb] at h
    refine ⟨B, ?_⟩
    have h2 : (Except.ok (Spec.Protocol.on_block C P st B,
        l ++ [Spec.NamedObject.block B]) :
        DC.DRE (Spec.Store V × List (Spec.NamedObject V))) =
          Except.ok (st', l') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1.symm, h2.2.symm⟩

omit [Inhabited V] in
/-- What a successful run of the spec's Goldfish vote duty does: nothing, or it admits a vote `u`
    with `on_goldfish_vote_checked` and broadcasts it. -/
theorem goldfish_vote_run {C : Spec.Config} {P : Spec.Provisional V} {v : V}
    {st st' : Spec.Store V} {l l' : List (Spec.NamedObject V)}
    (h : (Spec.Protocol.goldfish_vote C P v st).run l = .ok (st', l')) :
    (st' = st ∧ l' = l) ∨ ∃ u : Spec.GoldfishVote V,
      st' = Spec.Protocol.on_goldfish_vote_checked P st u ∧
        l' = l ++ [Spec.NamedObject.gfVote u] := by
  unfold Spec.Protocol.goldfish_vote at h
  dsimp only at h
  cases h1 : Spec.Protocol.voter_view C st st.s with
  | error e => rw [h1] at h; cases h
  | ok votes =>
  simp only [h1, liftM_ok_bind] at h
  cases h2 : Spec.Protocol.voter_support_view C st st.s with
  | error e => rw [h2] at h; cases h
  | ok sv =>
  simp only [h2, liftM_ok_bind] at h
  cases h3 : Spec.Protocol.voter_filtered_block_tree C st st.s with
  | error e => rw [h3] at h; cases h
  | ok tree =>
  simp only [h3, liftM_ok_bind] at h
  cases h4 : Spec.Protocol.get_head_in_tree_with_layer C st tree votes sv (st.s - 1) with
  | error e => rw [h4] at h; cases h
  | ok H =>
  simp only [h4, liftM_ok_bind] at h
  by_cases hc : v ∈ P.committee st.s
  · right
    refine ⟨⟨v, st.s, H.root⟩, ?_⟩
    rw [if_pos hc] at h
    have h2' : (Except.ok (Spec.Protocol.on_goldfish_vote_checked P st ⟨v, st.s, H.root⟩,
        l ++ [Spec.NamedObject.gfVote ⟨v, st.s, H.root⟩]) :
        DC.DRE (Spec.Store V × List (Spec.NamedObject V))) =
          Except.ok (st', l') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2'
    exact ⟨h2'.1.symm, h2'.2.symm⟩
  · left
    rw [if_neg hc] at h
    have h2' : (Except.ok (st, l) :
        DC.DRE (Spec.Store V × List (Spec.NamedObject V))) =
          Except.ok (st', l') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2'
    exact ⟨h2'.1.symm, h2'.2.symm⟩

omit [Inhabited V] in
/-- What a successful run of the spec's attestation duty does: it builds an attestation with
    `build_attestation`, admits it into the store and broadcasts it. -/
theorem attest_run {C : Spec.Config} {v : V} {st st' : Spec.Store V}
    {sh sh' : Spec.SigningHistory} {l l' : List (Spec.NamedObject V)}
    (h : (Spec.Protocol.attest C v st sh).run l = .ok ((st', sh'), l')) :
    ∃ row : Spec.Attestation V,
      Spec.Protocol.build_attestation C v st sh = .ok (sh', row) ∧
      st' = Spec.Protocol.admit_attestation C st row ∧
      l' = l ++ [Spec.NamedObject.attest row] := by
  unfold Spec.Protocol.attest at h
  dsimp only at h
  cases hb : Spec.Protocol.build_attestation C v st sh with
  | error e => rw [hb] at h; cases h
  | ok p =>
  rw [hb] at h
  obtain ⟨sh1, row⟩ := p
  have h2 : (Except.ok ((Spec.Protocol.admit_attestation C st row, sh1),
      l ++ [Spec.NamedObject.attest row]) :
      DC.DRE ((Spec.Store V × Spec.SigningHistory) ×
        List (Spec.NamedObject V))) = Except.ok ((st', sh'), l') := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨h21, h22⟩, h23⟩ := h2
  subst h21 h22 h23
  exact ⟨row, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `x >>= f` run from `l` gives `b` exactly when `x` gives some `a` and `f a` gives `b`. -/
theorem run_bind_ok {α β : Type} (x : Spec.DREB V α) (f : α → Spec.DREB V β)
    (l : List (Spec.NamedObject V)) (b : β × List (Spec.NamedObject V)) :
    (x >>= f).run l = .ok b ↔ ∃ a l', x.run l = .ok (a, l') ∧ (f a).run l' = .ok b := by
  rw [StateT.run_bind]
  cases hx : x.run l with
  | error e =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro a l' h
    cases h
  | ok p =>
    obtain ⟨a, l'⟩ := p
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨a, l', ⟨rfl, rfl⟩, h⟩
    · rintro ⟨a', l'', ⟨rfl, rfl⟩, h⟩
      exact h

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A `DRE` routine lifted into `DREB` gives `a` and keeps the list exactly when the routine answers
    `a`. -/
theorem liftM_run {α : Type} (x : DC.DRE α) (l : List (Spec.NamedObject V)) (a : α)
    (l' : List (Spec.NamedObject V)) :
    ((liftM x : Spec.DREB V α).run l = .ok (a, l')) ↔ x = .ok a ∧ l' = l := by
  cases x with
  | error e =>
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; cases h
  | ok b =>
    have : ((liftM (Except.ok b : DC.DRE α) : Spec.DREB V α).run l) = .ok (b, l) := rfl
    rw [this]
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `pure a` run in `DREB` answers `a` and sends nothing. -/
theorem pure_run {α : Type} (a : α) (l : List (Spec.NamedObject V))
    (b : α × List (Spec.NamedObject V)) :
    ((pure a : Spec.DREB V α).run l = .ok b) ↔ b = (a, l) := by
  have : ((pure a : Spec.DREB V α).run l) = .ok (a, l) := rfl
  rw [this]
  simp only [Except.ok.injEq]
  exact eq_comm

/-- Run `f` on `a` when `c` holds, and return `a` otherwise. -/
def optStep {α : Type} (c : Prop) [Decidable c] (f : α → Spec.DREB V α) (a : α) :
    Spec.DREB V α :=
  if c then f a else pure a

/-- The spec's tick written as a chain of optional steps, each a separate bind: record the wake,
    update the grades, set the clock, then the four optional duties, then clip the saved grades. -/
def tickChain (C : Spec.Config) (P : Spec.Provisional V)
    (X : Spec.External V) (n : Spec.NodeState V) (t : Spec.Time) :
    Spec.DREB V (Spec.NodeState V) := do
  let n0 := Spec.record_awake n t
  let st0 ← liftM (Spec.Protocol.update_grades C P n0.st t)
  let st1 : Spec.Store V := { st0 with t := t, s := C.slotOf t }
  let st2 ← optStep (0 < C.slotOf t ∧ (decide (t = C.proposal_time (C.slotOf t)) &&
      decide (P.proposer (C.slotOf t) = n0.v) &&
      n0.awake_since (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true)
      (Spec.Protocol.propose_block C P X n0.v) st1
  let st3 ← optStep (0 < C.slotOf t ∧ (decide (t = C.vote_time (C.slotOf t)) &&
      n0.awake_since (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true)
      (Spec.Protocol.goldfish_vote C P n0.v) st2
  let st4 ← optStep (0 < C.slotOf t ∧ (decide (t = C.gf_confirmation_time (C.slotOf t)) &&
      n0.awake_since (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true)
      (fun st => liftM (Spec.Protocol.update_confirmation C st (C.slotOf t - 1))) st3
  let p ← optStep ((decide (t = C.round_attestation_time (C.round_of (C.slotOf t))) &&
      n0.awake_since (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true)
      (fun p => Spec.Protocol.attest C n0.v p.1 p.2) (st4, n0.signingHistory)
  pure { v := n0.v, st := Spec.make_grades_compatible_with_finalized p.1,
         signingHistory := p.2, awakeSince := n0.awakeSince }

omit [Inhabited V] in
/-- The spec's tick equals `tickChain`. -/
theorem tick_eq_tickChain (C : Spec.Config) (P : Spec.Provisional V)
    (X : Spec.External V) (n : Spec.NodeState V) (t : Spec.Time) :
    Spec.tick C P X n t = tickChain C P X n t := by
  by_cases hs : 0 < C.slotOf t
  · simp only [Spec.tick, tickChain, optStep, gt_iff_lt, hs, true_and, if_true]
    split_ifs <;> rfl
  · simp only [Spec.tick, tickChain, optStep, gt_iff_lt, hs, false_and, if_false]
    split_ifs <;> rfl

omit [Inhabited V] in
/-- What a successful run of the spec's tick does: its node state comes from the grades update, the
    clock set, an optional proposal, an optional Goldfish vote, an optional confirmation update and
    an optional attestation, and it sent what those duties sent. -/
theorem tick_run_ok {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 st3 st4 st5 : Spec.Store V) (sh5 : Spec.SigningHistory)
      (l1 l2 : List (Spec.NamedObject V)),
      Spec.Protocol.update_grades C P (Spec.record_awake n t).st t = .ok st0 ∧
      ((∃ B : Spec.Block V, st2 = Spec.Protocol.on_block C P
          { st0 with t := t, s := C.slotOf t } B ∧ l1 = [Spec.NamedObject.block B]) ∨
        (st2 = { st0 with t := t, s := C.slotOf t } ∧ l1 = [])) ∧
      ((∃ u : Spec.GoldfishVote V,
          st3 = Spec.Protocol.on_goldfish_vote_checked P st2 u ∧
          l2 = l1 ++ [Spec.NamedObject.gfVote u]) ∨ (st3 = st2 ∧ l2 = l1)) ∧
      ((∃ s', Spec.Protocol.update_confirmation C st3 s' = .ok st4) ∨ st4 = st3) ∧
      ((∃ row : Spec.Attestation V, Spec.Protocol.build_attestation C
            (Spec.record_awake n t).v st4
              (Spec.record_awake n t).signingHistory = .ok (sh5, row) ∧
          st5 = Spec.Protocol.admit_attestation C st4 row ∧
          sent = l2 ++ [Spec.NamedObject.attest row]) ∨
        (st5 = st4 ∧ sh5 = (Spec.record_awake n t).signingHistory ∧ sent = l2)) ∧
      n' = { v := (Spec.record_awake n t).v,
             st := Spec.make_grades_compatible_with_finalized st5,
             signingHistory := sh5,
             awakeSince := (Spec.record_awake n t).awakeSince } := by
  rw [tick_eq_tickChain] at h
  unfold tickChain at h
  dsimp only at h
  rw [run_bind_ok] at h
  obtain ⟨st0, l0, h0, h⟩ := h
  rw [liftM_run] at h0
  obtain ⟨h0, rfl⟩ := h0
  rw [run_bind_ok] at h
  obtain ⟨st2, l1, h1, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨st3, l2, h2, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨st4, l3, h3, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨⟨st5, sh5⟩, l4, h4, h⟩ := h
  unfold optStep at h1 h2 h3 h4
  rw [pure_run] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h3' : ((∃ s', Spec.Protocol.update_confirmation C st3 s' = .ok st4) ∨
      st4 = st3) ∧ l3 = l2 := by
    split_ifs at h3
    · rw [liftM_run] at h3
      exact ⟨Or.inl ⟨_, h3.1⟩, h3.2⟩
    · rw [pure_run] at h3
      simp only [Prod.mk.injEq] at h3
      exact ⟨Or.inr h3.1, h3.2⟩
  obtain ⟨h3c, rfl⟩ := h3'
  refine ⟨st0, st2, st3, st4, st5, sh5, l1, l3, h0, ?_, ?_, h3c, ?_, rfl⟩
  · split_ifs at h1
    · obtain ⟨B, rfl, rfl⟩ := propose_block_run h1
      exact Or.inl ⟨B, rfl, rfl⟩
    · rw [pure_run] at h1
      simp only [Prod.mk.injEq] at h1
      exact Or.inr ⟨h1.1, h1.2⟩
  · split_ifs at h2
    · rcases goldfish_vote_run h2 with ⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨u, rfl, rfl⟩
    · rw [pure_run] at h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inr ⟨h2.1, h2.2⟩
  · split_ifs at h4
    · obtain ⟨row, hb, rfl, rfl⟩ := attest_run h4
      exact Or.inl ⟨row, hb, rfl, rfl⟩
    · rw [pure_run] at h4
      simp only [Prod.mk.injEq] at h4
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
      exact Or.inr ⟨rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.advance_to_round c r` has round `r`. -/
theorem advance_to_round_round (c : Spec.SavedGrades V) (r : Spec.Round) :
    (Spec.Protocol.advance_to_round c r).round = r := by
  unfold Spec.Protocol.advance_to_round
  split_ifs with h1
  · exact h1.symm
  · rfl
  · rfl

omit [Inhabited V] in
/-- The spec's `Protocol.update_grades` writes only the saved grades, and brings them to the round
    of `t`'s slot. -/
theorem update_grades_ok {C : Spec.Config} {P : Spec.Provisional V}
    {st st0 : Spec.Store V} {t : Spec.Time}
    (h : Spec.Protocol.update_grades C P st t = .ok st0) :
    st0 = { st with saved_grades := st0.saved_grades } ∧
      st0.saved_grades.round = C.round_of (C.slotOf t) := by
  simp only [Spec.Protocol.update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := dre_bind_ok h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    exact ⟨rfl, advance_to_round_round _ _⟩

omit [Inhabited V] in
/-- The spec's `Protocol.update_confirmation` writes only `live_confirmed`, `latest_stable` and
    `latest_confirmed`. -/
theorem update_confirmation_ok {C : Spec.Config} {st st' : Spec.Store V}
    {s : Spec.Slot}
    (h : Spec.Protocol.update_confirmation C st s = .ok st') :
    st' = { st with live_confirmed := st'.live_confirmed, latest_stable := st'.latest_stable, latest_confirmed := st'.latest_confirmed } := by
  simp only [Spec.Protocol.update_confirmation] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := dre_bind_ok h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `record_awake` writes only `awakeSince`. -/
theorem record_awake_eq (n : Spec.NodeState V) (t : Spec.Time) :
    Spec.record_awake n t =
      { n with awakeSince := (Spec.record_awake n t).awakeSince } := by
  simp only [Spec.record_awake, Id.run]
  split_ifs <;> rfl

/-- The member `tick` of `Model.specDraftBase` can return `out` exactly when the spec's tick, run
    from the empty list, answers with `out`'s node state and objects whose images are those `out`
    sends. -/
theorem tick_returns_iff (S : Setup V) (v : V) (n : Spec.NodeState V) (t : Time)
    (out : Spec.NodeState V × List (NamedObject V)) :
    (Model.specDraftBase (V := V)).tick S v n t ⇢ out ↔
      ∃ n' sent, (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X n
          t).run [] = .ok (n', sent) ∧ out = (n', sent.map Spec.NamedObject.toProof) := by
  show Returns (successOutcomes _) out ↔ _
  rw [returns_successOutcomes]
  cases h : (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X n t).run []
    with
  | error e =>
    simp only [Except.map, reduceCtorEq, false_iff, not_exists, not_and]
    intro n' sent h'
    cases h'
  | ok p =>
    obtain ⟨n', sent⟩ := p
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨n', sent, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨n'', sent', ⟨rfl, rfl⟩, rfl⟩
      rfl

/-- The store `b` is reached from `a` by receipts of objects (the member `receipt_process`) and
    confirmation updates (`Protocol.update_confirmation`), in any number and order. -/
inductive TickSteps (S : Setup V) : Spec.Store V → Spec.Store V → Prop
  | refl (st : Spec.Store V) : TickSteps S st st
  | receipt (st st' : Spec.Store V) (o : NamedObject V) :
      TickSteps S (Member.receipt_process S st o) st' → TickSteps S st st'
  | confirm (st st' st'' : Spec.Store V) (s : Slot) :
      Spec.Protocol.update_confirmation (Setup.toSpec S).C st s = .ok st'' →
        TickSteps S st'' st' → TickSteps S st st'

omit [Inhabited V] in
/-- A reflexive and transitive relation that every receipt and every confirmation update satisfies
    holds along `TickSteps`. -/
theorem TickSteps.rel {S : Setup V} (R : Spec.Store V → Spec.Store V → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hrec : ∀ st o, R st (Member.receipt_process S st o))
    (hconf : ∀ st s st', Spec.Protocol.update_confirmation (Setup.toSpec S).C st s =
      .ok st' → R st st') {a b : Spec.Store V} (h : TickSteps S a b) : R a b := by
  induction h with
  | refl st => exact hrefl st
  | receipt st st' o _ ih => exact htrans _ _ _ (hrec st o) ih
  | confirm st st' st'' s hc _ ih => exact htrans _ _ _ (hconf st s st'' hc) ih

omit [Inhabited V] in
/-- `TickSteps` is transitive. -/
theorem TickSteps.trans {S : Setup V} {a b c : Spec.Store V} (h1 : TickSteps S a b)
    (h2 : TickSteps S b c) : TickSteps S a c := by
  induction h1 with
  | refl st => exact h2
  | receipt st st' o _ ih => exact TickSteps.receipt _ _ o (ih h2)
  | confirm st st' st'' s hc _ ih => exact TickSteps.confirm _ _ _ s hc (ih h2)

omit [Inhabited V] in
/-- `TickSteps` keeps the saved grades. -/
theorem TickSteps.saved_grades {S : Setup V} {a b : Spec.Store V} (h : TickSteps S a b) :
    b.saved_grades = a.saved_grades :=
  TickSteps.rel (fun a b => b.saved_grades = a.saved_grades) (fun _ => rfl)
    (fun _ _ _ h1 h2 => h2.trans h1) (fun st o => receipt_process_saved_grades S st o)
    (fun st s st' hc => by rw [update_confirmation_ok hc]) h

omit [Inhabited V] in
/-- `on_block` at the parameters read from `S` is the member `receipt_process` on the named image of
    the block. -/
theorem on_block_eq_receipt (S : Setup V) (st : Spec.Store V)
    (B : Spec.Block V) :
    Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st B =
      Member.receipt_process S st (.block B.toProofNamed) := by
  show _ = Spec.Protocol.on_block _ _ st (Spec.Block.toSpecNamed B.toProofNamed)
  rw [Spec.Block.toSpecNamed_toProofNamed]
  rfl

omit [Inhabited V] in
/-- `on_goldfish_vote_checked` at the parameters read from `S` is the member `receipt_process` on
    the image of the vote. -/
theorem on_goldfish_vote_checked_eq_receipt (S : Setup V) (st : Spec.Store V)
    (u : Spec.GoldfishVote V) :
    Spec.Protocol.on_goldfish_vote_checked (Setup.toSpec S).P st u =
      Member.receipt_process S st (.gfVote u.toProof) := by
  show _ = Spec.Protocol.on_goldfish_vote_checked _ st
    (Spec.GoldfishVote.toSpec u.toProof)
  rw [Spec.GoldfishVote.toSpec_toProof]
  rfl

omit [Inhabited V] in
/-- `admit_attestation` at the parameters read from `S` is the member `receipt_process` on the named
    image of the attestation. -/
theorem admit_attestation_eq_receipt (S : Setup V) (st : Spec.Store V)
    (a : Spec.Attestation V) :
    Spec.Protocol.admit_attestation (Setup.toSpec S).C st a =
      Member.receipt_process S st (.attest a.toProofNamed) := by
  show _ = Spec.Protocol.admit_attestation _ st
    (Spec.Attestation.toSpecNamed a.toProofNamed)
  rw [Spec.Attestation.toSpecNamed_toProofNamed]
  rfl

/-- The store of every outcome of the member `tick`: the node's store with its saved grades replaced
    and its clock set, then `TickSteps`, then the clip of the saved grades; the saved grades are at
    the round of `t`'s slot. -/
theorem tick_store {S : Setup V} {v : V} {n : Spec.NodeState V} {t : Time}
    {out : Spec.NodeState V × List (NamedObject V)}
    (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out) :
    ∃ (sg : Spec.SavedGrades V) (st5 : Spec.Store V),
      TickSteps S { n.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } st5 ∧
      out.1.st = Spec.make_grades_compatible_with_finalized st5 ∧
      st5.saved_grades = sg ∧ sg.round = (Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t) := by
  obtain ⟨n', sent, hrun, rfl⟩ := (tick_returns_iff S v n t out).mp hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, h1, h2, h3, h4, rfl⟩ := tick_run_ok hrun
  have hst : (Spec.record_awake n t).st = n.st := by rw [record_awake_eq]
  rw [hst] at h0
  obtain ⟨h0e, h0r⟩ := update_grades_ok h0
  have hst1 : ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V) =
      { n.st with saved_grades := st0.saved_grades, t := t, s := (Setup.toSpec S).C.slotOf t } := by
    rw [h0e]
  rw [hst1] at h1
  have hsteps : TickSteps S { n.st with saved_grades := st0.saved_grades, t := t, s := (Setup.toSpec S).C.slotOf t } st5 := by
    have s1 : TickSteps S { n.st with saved_grades := st0.saved_grades, t := t, s := (Setup.toSpec S).C.slotOf t } st2 := by
      rcases h1 with ⟨B, rfl, -⟩ | ⟨rfl, -⟩
      · rw [on_block_eq_receipt]
        exact TickSteps.receipt _ _ _ (TickSteps.refl _)
      · exact TickSteps.refl _
    have s2 : TickSteps S st2 st3 := by
      rcases h2 with ⟨u, rfl, -⟩ | ⟨rfl, -⟩
      · rw [on_goldfish_vote_checked_eq_receipt]
        exact TickSteps.receipt _ _ _ (TickSteps.refl _)
      · exact TickSteps.refl _
    have s3 : TickSteps S st3 st4 := by
      rcases h3 with ⟨s', hc⟩ | rfl
      · exact TickSteps.confirm _ _ _ s' hc (TickSteps.refl _)
      · exact TickSteps.refl _
    have s4 : TickSteps S st4 st5 := by
      rcases h4 with ⟨row, -, rfl, -⟩ | ⟨rfl, -, -⟩
      · rw [admit_attestation_eq_receipt]
        exact TickSteps.receipt _ _ _ (TickSteps.refl _)
      · exact TickSteps.refl _
    exact s1.trans (s2.trans (s3.trans s4))
  refine ⟨st0.saved_grades, st5, hsteps, rfl, hsteps.saved_grades, h0r⟩

/-- The node state with the store `st`, the default validator, the initial signing history and no
    `awakeSince`. -/
def nodeOf (st : Spec.Store V) : Spec.NodeState V :=
  ⟨default, st, Spec.SigningHistory.initial, none⟩

/-- `receiveNamedObject` at `nodeOf st` holds the clipped store of the member `receipt_process`. -/
theorem receive_nodeOf (S : Setup V) (st : Spec.Store V) (o : NamedObject V) :
    receiveNamedObject S (nodeOf st) o =
      { nodeOf st with st := Spec.make_grades_compatible_with_finalized (Member.receipt_process S st o) } :=
  receiveNamedObject_eq S (nodeOf st) o

/-- A reflexive and transitive relation that the clock set, every receipt, every confirmation update
    and the final clip satisfy holds between the store of the node and the store of every outcome of
    its tick. -/
theorem tick_store_rel {S : Setup V} {v : V} {n : Spec.NodeState V} {t : Time}
    {out : Spec.NodeState V × List (NamedObject V)}
    (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out)
    (R : Spec.Store V → Spec.Store V → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hrec : ∀ st o, R st (Member.receipt_process S st o))
    (hconf : ∀ st s st', Spec.Protocol.update_confirmation (Setup.toSpec S).C st s =
      .ok st' → R st st')
    (hstart : ∀ sg, R n.st { n.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t })
    (hend : ∀ st, R st (Spec.make_grades_compatible_with_finalized st)) :
    R n.st out.1.st := by
  obtain ⟨sg, st5, hsteps, hst, -, -⟩ := tick_store hout
  rw [hst]
  exact htrans _ _ _ (htrans _ _ _ (hstart sg) (hsteps.rel R hrefl htrans hrec hconf)) (hend st5)

/-- The field `tick_h_max_mono` of `NodeFacts` at `Model.specDraftBase`: every outcome `out` of
    `v`'s tick at `t` from `n` has an `h_max` at least `n`'s. -/
theorem specDraftBase_tick_h_max_mono : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    n.st.core.h_max ≤ out.1.st.core.h_max := by
  intro S v n t out hout
  refine tick_store_rel hout (fun a b => a.h_max ≤ b.h_max) (fun _ => le_refl _)
    (fun _ _ _ h1 h2 => le_trans h1 h2) ?_ ?_ (fun _ => le_refl _) (fun _ => le_refl _)
  · intro st o
    have h := specDraftBase_process_h_max_mono S (nodeOf st) o _ ((process_returns_iff _ _ _ _).mpr rfl)
    rw [receive_nodeOf] at h
    exact h
  · intro st s st' hc
    rw [update_confirmation_ok hc]

/-- The field `tick_h_max_mono` of `NodeFacts` at `Model.specDraft`: every outcome `out` of `v`'s
    tick at `t` from `n` has an `h_max` at least `n`'s. -/
theorem specDraft_tick_h_max_mono : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    n.st.core.h_max ≤ out.1.st.core.h_max :=
  fun S v n t out hout => specDraftBase_tick_h_max_mono S v n.val t (out.1.val, out.2) hout

/-- The field `node_tick_F` of `NodeFacts` at `Model.specDraftBase`: for every outcome `out` of
    `v`'s tick at `t` from `n`, `n`'s finalized block is an ancestor of, or equal to, `out.1`'s. -/
theorem specDraftBase_node_tick_F : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    Block.Preceq n.st.core.F out.1.st.core.F := by
  intro S v n t out hout
  refine tick_store_rel (R := fun a b => Block.Preceq a.F.toProof b.F.toProof) hout
    (fun _ => Proofs.ModelProperties.Preceq_self _)
    (fun _ _ _ h1 h2 => Proofs.ModelProperties.Preceq_trans h1 h2) ?_ ?_
    (fun _ => Proofs.ModelProperties.Preceq_self _) (fun _ => Proofs.ModelProperties.Preceq_self _)
  · intro st o
    have h := specDraftBase_node_process_F S (nodeOf st) o _ ((process_returns_iff _ _ _ _).mpr rfl)
    rw [receive_nodeOf] at h
    exact h
  · intro st s st' hc
    rw [update_confirmation_ok hc]
    exact Proofs.ModelProperties.Preceq_self _

/-- The field `node_tick_F` of `NodeFacts` at `Model.specDraft`: for every outcome `out` of `v`'s
    tick at `t` from `n`, `n`'s finalized block is an ancestor of, or equal to, `out.1`'s. -/
theorem specDraft_node_tick_F : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    Block.Preceq n.st.core.F out.1.st.core.F :=
  fun S v n t out hout => specDraftBase_node_tick_F S v n.val t (out.1.val, out.2) hout

omit [Inhabited V] in
/-- The slot of a time under the spec's parameters read from `S` is `S.E.slotOf t`. -/
theorem slotOf_eq (S : Setup V) (t : Time) : (Setup.toSpec S).C.slotOf t = S.E.slotOf t := by
  simp only [Spec.Config.slotOf, Env.slotOf, slotOfTime]
  rfl

/-- The field `tick_clock` of `NodeFacts` at `Model.specDraftBase`: for every outcome `out` of `v`'s
    tick at `t` from `n`, `out.1`'s store part has the clock `t` and the slot `S.E.slotOf t`. -/
theorem specDraftBase_tick_clock : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    out.1.st.core.t = t ∧ out.1.st.core.s = S.E.slotOf t := by
  intro S v n t out hout
  obtain ⟨sg, st5, hsteps, hst, -, -⟩ := tick_store hout
  have h := hsteps.rel (fun a b => b.t = a.t ∧ b.s = a.s) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩)
    (fun st o => by
      have h := specDraftBase_process_clock S (nodeOf st) o _ ((process_returns_iff _ _ _ _).mpr rfl)
      rw [receive_nodeOf] at h
      exact h)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact ⟨rfl, rfl⟩)
  show (Spec.NodeState.st out.1).t = t ∧ (Spec.NodeState.st out.1).s = S.E.slotOf t
  rw [hst, ← slotOf_eq]
  exact h

/-- The field `tick_clock` of `NodeFacts` at `Model.specDraft`: for every outcome `out` of `v`'s
    tick at `t` from `n`, `out.1`'s store part has the clock `t` and the slot `S.E.slotOf t`. -/
theorem specDraft_tick_clock : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    out.1.st.core.t = t ∧ out.1.st.core.s = S.E.slotOf t :=
  fun S v n t out hout => specDraftBase_tick_clock S v n.val t (out.1.val, out.2) hout

/-- The field `tick_cache_round` of `NodeFacts` at `Model.specDraftBase`: for every outcome `out` of
    `v`'s tick at `t` from `n`, the round of `out.1`'s grade cache is the round of the slot of `t`. -/
theorem specDraftBase_tick_cache_round : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    out.1.cache.round = (Model.specDraftBase (V := V)).round_of S.hc (S.E.slotOf t) := by
  intro S v n t out hout
  obtain ⟨sg, st5, hsteps, hst, hsg, hround⟩ := tick_store hout
  show (Spec.NodeState.st out.1).saved_grades.round = _
  rw [hst]
  show st5.saved_grades.round = _
  rw [hsg, hround, slotOf_eq]
  rfl

/-- The field `tick_cache_round` of `NodeFacts` at `Model.specDraft`: for every outcome `out` of
    `v`'s tick at `t` from `n`, the round of `out.1`'s grade cache is the round of the slot of `t`. -/
theorem specDraft_tick_cache_round : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    out.1.cache.round = (Model.specDraft (V := V)).round_of S.hc (S.E.slotOf t) :=
  fun S v n t out hout => specDraftBase_tick_cache_round S v n.val t (out.1.val, out.2) hout

/-- The spec's attestation input as the input of `NamedRecord.create`, the roots mapped by
    `toProof`. -/
def toInput (x : Spec.Protocol.AttestationInput V) : Protocol.NamedRecord.Input V :=
  ⟨x.val_index, x.round, x.confirmed.map Spec.BlockId.toProof,
    x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2)), x.h_j, x.J.toProof, x.h_F⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.rememberTimeout`, mapped, is `NamedRecord.rememberTimeout` at the mapped
    arguments. -/
theorem rememberTimeout_map (history : Finset (Height × Spec.BlockId))
    (pair : Spec.HeightPair) :
    (Spec.Protocol.rememberTimeout history pair).map
        Spec.SigningHistory.timeoutToProofEmb =
      Protocol.NamedRecord.rememberTimeout
        (history.map Spec.SigningHistory.timeoutToProofEmb) pair.toProofNamed := by
  cases pair with
  | empty => simp [Spec.Protocol.rememberTimeout, Protocol.NamedRecord.rememberTimeout,
      Spec.HeightPair.toProofNamed]
  | vote h entry timeout =>
    cases timeout
    · simp [Spec.Protocol.rememberTimeout, Protocol.NamedRecord.rememberTimeout,
        Spec.HeightPair.toProofNamed]
    · simp only [Spec.Protocol.rememberTimeout, Protocol.NamedRecord.rememberTimeout,
        Spec.HeightPair.toProofNamed, Finset.map_union, Finset.map_singleton,
        Spec.SigningHistory.timeoutToProofEmb_apply]
      rw [Finset.insert_eq, Finset.union_comm]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.record_attestation` keeps the timeout votes `timeouts`. -/
theorem record_attestation_timeouts (sh : Spec.SigningHistory)
    (a : Spec.Attestation V) :
    (Spec.Protocol.record_attestation sh a).timeouts = sh.timeouts := by
  simp only [Spec.Protocol.record_attestation, Id.run]
  split_ifs <;> rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `NamedRecord.encodeHeight` at the mapped input fields and the image of the height pair that
    `Protocol.height_pair` decides is the named image of that height pair. -/
theorem encodeHeight_height_pair (sh : Spec.SigningHistory)
    (fields : Option (Height × Spec.BlockId × Bool))
    (fp : Option Spec.FinalityPair) :
    Protocol.NamedRecord.encodeHeight (fields.map (fun f => (f.1, f.2.1.toProof, f.2.2)))
        (Spec.Protocol.height_pair sh fields fp).toProof =
      (Spec.Protocol.height_pair sh fields fp).toProofNamed := by
  have hv : ∀ (a : Height × Spec.BlockId × Bool) (h : some a ≠ none),
      (some a).value h = a := fun _ _ => rfl
  rcases fields with _ | ⟨h_c, T_c, ν⟩
  · simp [Spec.Protocol.height_pair, Id.run, Protocol.NamedRecord.encodeHeight,
      Spec.HeightPair.toProof, Spec.HeightPair.toProofNamed, pure]
  · simp only [Spec.Protocol.height_pair, Id.run]
    split_ifs <;> simp [Protocol.NamedRecord.encodeHeight, Spec.HeightPair.toProof,
      Spec.HeightPair.toProofNamed, pure, hv]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.create`, mapped, is `NamedRecord.create` at `toInput x`. -/
theorem toProof_create (sh : Spec.SigningHistory)
    (x : Spec.Protocol.AttestationInput V) :
    (Spec.Protocol.create sh x).1.toProof =
        (Protocol.NamedRecord.create sh.toProof (toInput x)).1 ∧
      (Spec.Protocol.create sh x).2.toProofNamed =
        (Protocol.NamedRecord.create sh.toProof (toInput x)).2 := by
  have hA := toProof_create_attestation sh x.val_index x.round x.confirmed x.fields x.h_j x.J x.h_F
  have hE := encodeHeight_height_pair sh x.fields
    (Spec.Protocol.finality_pair sh x.h_j x.J x.h_F)
  have hT : (Spec.Protocol.create_attestation sh x.val_index x.round x.confirmed x.fields
      x.h_j x.J x.h_F).1.timeouts = sh.timeouts := by
    simp only [Spec.Protocol.create_attestation, Id.run]
    exact record_attestation_timeouts _ _
  have hP : (Spec.Protocol.create_attestation sh x.val_index x.round x.confirmed x.fields
      x.h_j x.J x.h_F).2.height_pair = Spec.Protocol.height_pair sh x.fields
        (Spec.Protocol.finality_pair sh x.h_j x.J x.h_F) := rfl
  simp only [Spec.Protocol.create, Protocol.NamedRecord.create,
    Protocol.NamedRecord.legacyCreate, toInput, Id.run, hA, pure]
  rw [← hP] at hE
  generalize Spec.Protocol.create_attestation sh x.val_index x.round x.confirmed x.fields
    x.h_j x.J x.h_F = p at hE hT
  obtain ⟨sh1, a⟩ := p
  simp only at hE hT
  constructor
  · simp only [Spec.SigningHistory.toProof, Prod.map, hT,
      Protocol.NamedRecord.encodeRow, Spec.Attestation.toProof]
    rw [hE, rememberTimeout_map]
  · simp only [Prod.map, Protocol.NamedRecord.encodeRow, Spec.Attestation.toProofNamed,
      Spec.Attestation.toProof, hE]

/-- The signing history of every outcome of the member `tick` is the node's, or the one
    `Protocol.create` returns on some attestation input, in which case the attestation `create`
    returns is among the objects sent. -/
theorem tick_signing {S : Setup V} {v : V} {n : Spec.NodeState V} {t : Time}
    {out : Spec.NodeState V × List (NamedObject V)}
    (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out) :
    out.1.signingHistory = n.signingHistory ∨
      ∃ x : Spec.Protocol.AttestationInput V,
        out.1.signingHistory = (Spec.Protocol.create n.signingHistory x).1 ∧
        NamedObject.attest (Spec.Protocol.create n.signingHistory x).2.toProofNamed ∈ out.2 := by
  obtain ⟨n', sent, hrun, rfl⟩ := (tick_returns_iff S v n t out).mp hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, -, -, -, -, h4, rfl⟩ := tick_run_ok hrun
  have hsh : (Spec.record_awake n t).signingHistory = n.signingHistory := by
    rw [record_awake_eq]
  have hv : (Spec.record_awake n t).v = n.v := by
    rw [record_awake_eq]
  rw [hsh, hv] at h4
  rcases h4 with ⟨row, hb, -, rfl⟩ | ⟨-, rfl, -⟩
  · right
    simp only [Spec.Protocol.build_attestation] at hb
    obtain ⟨x, -, hb⟩ := dre_bind_ok hb
    have hb' : Spec.Protocol.create n.signingHistory x = (sh5, row) := by
      have := hb
      simp only [pure, Except.pure, Except.ok.injEq] at this
      exact this
    refine ⟨x, by rw [hb'], ?_⟩
    rw [hb']
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inl rfl)
  · left
    rfl

/-- The field `timeout_mono_on_tick_emit` of `NodeFacts` at `Model.specDraftBase`: if `n`'s signing
    record holds a timeout entry at height `h`, so does the signing record of every outcome `out` of
    `v`'s tick at `t` from `n`. -/
theorem specDraftBase_timeout_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    {h : Height} (hs : n.record.legacy.timeout h = true)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    out.1.record.legacy.timeout h = true := by
  intro S v n t h hs out hout
  show (Spec.NodeState.signingHistory out.1).toProof.legacy.timeout h = true
  rcases tick_signing hout with heq | ⟨x, heq, -⟩
  · rw [heq]; exact hs
  · rw [heq, (toProof_create n.signingHistory x).1, Proofs.NamedRecord.create_legacy_records_erasure]
    exact Proofs.HealingSurface.record_attestation_timeout_mono _ hs

/-- The field `timeout_mono_on_tick_emit` of `NodeFacts` at `Model.specDraft`: if `n`'s signing
    record holds a timeout entry at height `h`, so does the signing record of every outcome `out` of
    `v`'s tick at `t` from `n`. -/
theorem specDraft_timeout_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    {h : Height} (hs : n.record.legacy.timeout h = true)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    out.1.record.legacy.timeout h = true :=
  fun S v n t {h} hs out hout => specDraftBase_timeout_mono_on_tick_emit S v n.val t (h := h) hs (out.1.val, out.2) hout

/-- The field `lock_mono_on_tick_emit` of `NodeFacts` at `Model.specDraftBase`: if `n`'s signing
    record holds the lock `T` at height `h`, so does the signing record of every outcome `out` of
    `v`'s tick at `t` from `n`. -/
theorem specDraftBase_lock_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hs : n.record.legacy.lock h = some T)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    out.1.record.legacy.lock h = some T := by
  intro S v n t h T hs out hout
  show (Spec.NodeState.signingHistory out.1).toProof.legacy.lock h = some T
  rcases tick_signing hout with heq | ⟨x, heq, -⟩
  · rw [heq]; exact hs
  · rw [heq, (toProof_create n.signingHistory x).1]
    simp only [Protocol.NamedRecord.create, Protocol.NamedRecord.legacyCreate]
    exact Proofs.HealingSurface.create_attestation_lock_mono
      (Λ := n.signingHistory.toProof.legacy) hs _ _ _ _ _ _ _

/-- The field `lock_mono_on_tick_emit` of `NodeFacts` at `Model.specDraft`: if `n`'s signing record
    holds the lock `T` at height `h`, so does the signing record of every outcome `out` of `v`'s
    tick at `t` from `n`. -/
theorem specDraft_lock_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hs : n.record.legacy.lock h = some T)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    out.1.record.legacy.lock h = some T :=
  fun S v n t {h} {T} hs out hout => specDraftBase_lock_mono_on_tick_emit S v n.val t (h := h) (T := T) hs (out.1.val, out.2) hout

/-- The field `target_mono_on_tick_emit` of `NodeFacts` at `Model.specDraftBase`: if `n`'s signing
    record holds the target `T` at height `h`, so does the signing record of every outcome `out` of
    `v`'s tick at `t` from `n`. -/
theorem specDraftBase_target_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hs : n.record.legacy.target h = some T)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    out.1.record.legacy.target h = some T := by
  intro S v n t h T hs out hout
  show (Spec.NodeState.signingHistory out.1).toProof.legacy.target h = some T
  rcases tick_signing hout with heq | ⟨x, heq, -⟩
  · rw [heq]; exact hs
  · rw [heq, (toProof_create n.signingHistory x).1, Proofs.NamedRecord.create_legacy_records_erasure]
    exact Proofs.HealingSurface.record_attestation_target_mono _ _ hs

/-- The field `target_mono_on_tick_emit` of `NodeFacts` at `Model.specDraft`: if `n`'s signing
    record holds the target `T` at height `h`, so does the signing record of every outcome `out` of
    `v`'s tick at `t` from `n`. -/
theorem specDraft_target_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hs : n.record.legacy.target h = some T)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    out.1.record.legacy.target h = some T :=
  fun S v n t {h} {T} hs out hout => specDraftBase_target_mono_on_tick_emit S v n.val t (h := h) (T := T) hs (out.1.val, out.2) hout

/-- The field `lockCompatible_on_tick_emit` of `NodeFacts` at `Model.specDraftBase`: if `n`'s
    signing record is `LockCompatible`, so is the signing record of every outcome `out` of `v`'s
    tick at `t` from `n`. -/
theorem specDraftBase_lockCompatible_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (hla : Restated.Vocabulary.Proofs.Records.LockCompatible (Model.specDraftBase (V := V)) n.record.legacy)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.Records.LockCompatible (Model.specDraftBase (V := V)) out.1.record.legacy := by
  intro S v n t hla out hout
  show Proofs.Records.LockCompatible (Spec.NodeState.signingHistory out.1).toProof.legacy
  rcases tick_signing hout with heq | ⟨x, heq, -⟩
  · rw [heq]; exact hla
  · rw [heq, (toProof_create n.signingHistory x).1]
    exact Proofs.NamedRecord.lock_compatible_create _ _ hla

/-- The field `lockCompatible_on_tick_emit` of `NodeFacts` at `Model.specDraft`: if `n`'s signing
    record is `LockCompatible`, so is the signing record of every outcome `out` of `v`'s tick at `t`
    from `n`. -/
theorem specDraft_lockCompatible_on_tick_emit : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (hla : Restated.Vocabulary.Proofs.Records.LockCompatible (Model.specDraft (V := V)) n.record.legacy)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.Records.LockCompatible (Model.specDraft (V := V)) out.1.record.legacy :=
  fun S v n t hla out hout => specDraftBase_lockCompatible_on_tick_emit S v n.val t hla (out.1.val, out.2) hout

/-- The field `record_invariant_tick` of `NodeFacts` at `Model.specDraftBase`: if `n`'s named
    signing record satisfies `NamedTickRecord.Invariant`, so does that of every outcome `out` of
    `v`'s tick at `t` from `n`. -/
theorem specDraftBase_record_invariant_tick : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (h : Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.specDraftBase (V := V)) n.record)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.specDraftBase (V := V)) out.1.record := by
  intro S v n t h out hout
  show Proofs.NamedRecord.HistoryConsistent (Spec.NodeState.signingHistory out.1).toProof ∧
    Proofs.Records.LockCompatible (Spec.NodeState.signingHistory out.1).toProof.legacy
  rcases tick_signing hout with heq | ⟨x, heq, -⟩
  · rw [heq]; exact h
  · rw [heq, (toProof_create n.signingHistory x).1]
    exact ⟨Proofs.NamedRecord.history_consistent_create _ _ h.1,
      Proofs.NamedRecord.lock_compatible_create _ _ h.2⟩

/-- The field `record_invariant_tick` of `NodeFacts` at `Model.specDraft`: if `n`'s named signing
    record satisfies `NamedTickRecord.Invariant`, so does that of every outcome `out` of `v`'s tick
    at `t` from `n`. -/
theorem specDraft_record_invariant_tick : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (h : Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.specDraft (V := V)) n.record)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.specDraft (V := V)) out.1.record :=
  fun S v n t h out hout => specDraftBase_record_invariant_tick S v n.val t h (out.1.val, out.2) hout

/-- The field `on_tick_emit_timeout_introduced` of `NodeFacts` at `Model.specDraftBase`: if `n`'s
    signing record holds no timeout entry at height `h` and the signing record of an outcome `out`
    of `v`'s tick at `t` from `n` holds one, then `out` sends an attestation whose height pair is
    the timeout at `h`. -/
theorem specDraftBase_on_tick_emit_timeout_introduced : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    {h : Height} (hpre : n.record.legacy.timeout h = false)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.timeout h = true),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.timeout h := by
  intro S v n t h hpre out hout hpost
  change (Spec.NodeState.signingHistory out.1).toProof.legacy.timeout h = true at hpost
  rcases tick_signing hout with heq | ⟨x, heq, hmem⟩
  · rw [heq] at hpost
    change n.signingHistory.toProof.legacy.timeout h = false at hpre
    rw [hpre] at hpost
    cases hpost
  · rw [heq, (toProof_create n.signingHistory x).1,
      Proofs.NamedRecord.create_legacy_records_erasure] at hpost
    refine ⟨_, hmem, ?_⟩
    rw [(toProof_create n.signingHistory x).2]
    exact Proofs.HealingSurface.record_attestation_timeout_introduced hpre hpost

/-- The field `on_tick_emit_timeout_introduced` of `NodeFacts` at `Model.specDraft`: if `n`'s
    signing record holds no timeout entry at height `h` and the signing record of an outcome `out`
    of `v`'s tick at `t` from `n` holds one, then `out` sends an attestation whose height pair is
    the timeout at `h`. -/
theorem specDraft_on_tick_emit_timeout_introduced : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    {h : Height} (hpre : n.record.legacy.timeout h = false)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.timeout h = true),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.timeout h :=
  fun S v n t {h} hpre out hout hpost => specDraftBase_on_tick_emit_timeout_introduced S v n.val t (h := h) hpre (out.1.val, out.2) hout hpost

/-- The field `on_tick_emit_lock_introduced` of `NodeFacts` at `Model.specDraftBase`: if `n`'s
    signing record holds no lock at height `h` and the signing record of an outcome `out` of `v`'s
    tick at `t` from `n` holds the lock `T` at `h`, then `out` sends an attestation whose finality
    pair is `(h, T)`. -/
theorem specDraftBase_on_tick_emit_lock_introduced : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hpre : n.record.legacy.lock h = none)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.lock h = some T),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.finality_pair = some ⟨h, T⟩ := by
  intro S v n t h T hpre out hout hpost
  change (Spec.NodeState.signingHistory out.1).toProof.legacy.lock h = some T at hpost
  rcases tick_signing hout with heq | ⟨x, heq, hmem⟩
  · rw [heq] at hpost
    change n.signingHistory.toProof.legacy.lock h = none at hpre
    rw [hpre] at hpost
    cases hpost
  · rw [heq, (toProof_create n.signingHistory x).1,
      Proofs.NamedRecord.create_legacy_records_erasure] at hpost
    refine ⟨_, hmem, ?_⟩
    rw [(toProof_create n.signingHistory x).2]
    have hl := Protocol.record_attestation_lock_introduced hpre hpost
    simpa only [NamedAttestation.erase] using hl

/-- The field `on_tick_emit_lock_introduced` of `NodeFacts` at `Model.specDraft`: if `n`'s signing
    record holds no lock at height `h` and the signing record of an outcome `out` of `v`'s tick at
    `t` from `n` holds the lock `T` at `h`, then `out` sends an attestation whose finality pair is
    `(h, T)`. -/
theorem specDraft_on_tick_emit_lock_introduced : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hpre : n.record.legacy.lock h = none)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.lock h = some T),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.finality_pair = some ⟨h, T⟩ :=
  fun S v n t {h} {T} hpre out hout hpost => specDraftBase_on_tick_emit_lock_introduced S v n.val t (h := h) (T := T) hpre (out.1.val, out.2) hout hpost

/-- The field `on_tick_emit_target_introduced` of `NodeFacts` at `Model.specDraftBase`: if `n`'s
    signing record holds no target at height `h` and the signing record of an outcome `out` of `v`'s
    tick at `t` from `n` holds the target `T` at `h`, then `out` sends an attestation whose height
    pair is the target `(h, T)`. -/
theorem specDraftBase_on_tick_emit_target_introduced : ∀ (S : Setup V) (v : V) (n : (Model.specDraftBase (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hpre : n.record.legacy.target h = none)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V)) (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.target h = some T),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.target h T := by
  intro S v n t h T hpre out hout hpost
  change (Spec.NodeState.signingHistory out.1).toProof.legacy.target h = some T at hpost
  rcases tick_signing hout with heq | ⟨x, heq, hmem⟩
  · rw [heq] at hpost
    change n.signingHistory.toProof.legacy.target h = none at hpre
    rw [hpre] at hpost
    cases hpost
  · rw [heq, (toProof_create n.signingHistory x).1,
      Proofs.NamedRecord.create_legacy_records_erasure] at hpost
    refine ⟨_, hmem, ?_⟩
    rw [(toProof_create n.signingHistory x).2]
    exact Protocol.record_attestation_target_introduced hpre hpost

/-- The field `on_tick_emit_target_introduced` of `NodeFacts` at `Model.specDraft`: if `n`'s signing
    record holds no target at height `h` and the signing record of an outcome `out` of `v`'s tick at
    `t` from `n` holds the target `T` at `h`, then `out` sends an attestation whose height pair is
    the target `(h, T)`. -/
theorem specDraft_on_tick_emit_target_introduced : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    {h : Height} {T : BlockId} (hpre : n.record.legacy.target h = none)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.target h = some T),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.target h T :=
  fun S v n t {h} {T} hpre out hout hpost => specDraftBase_on_tick_emit_target_introduced S v n.val t (h := h) (T := T) hpre (out.1.val, out.2) hout hpost

/-- The store of every outcome of the member `tick`, step by step: an optional receipt of a block,
    an optional receipt of a Goldfish vote, an optional confirmation update, an optional receipt of
    an attestation, then the clip of the saved grades. -/
theorem tick_chain {S : Setup V} {v : V} {n : Spec.NodeState V} {t : Time}
    {out : Spec.NodeState V × List (NamedObject V)}
    (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out) :
    ∃ (sg : Spec.SavedGrades V) (st2 st3 st4 st5 : Spec.Store V),
      (st2 = { n.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } ∨
        ∃ B : NamedBlock V, st2 = Member.receipt_process S
          { n.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } (.block B)) ∧
      (st3 = st2 ∨ ∃ u : GoldfishVote V, st3 = Member.receipt_process S st2 (.gfVote u)) ∧
      (st4 = st3 ∨ ∃ s, Spec.Protocol.update_confirmation (Setup.toSpec S).C st3 s = .ok st4) ∧
      (st5 = st4 ∨ ∃ a : NamedAttestation V, st5 = Member.receipt_process S st4 (.attest a)) ∧
      out.1.st = Spec.make_grades_compatible_with_finalized st5 := by
  obtain ⟨n', sent, hrun, rfl⟩ := (tick_returns_iff S v n t out).mp hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, h1, h2, h3, h4, rfl⟩ := tick_run_ok hrun
  have hst : (Spec.record_awake n t).st = n.st := by rw [record_awake_eq]
  rw [hst] at h0
  obtain ⟨h0e, -⟩ := update_grades_ok h0
  have hst1 : ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V) = { n.st with saved_grades := st0.saved_grades, t := t, s := (Setup.toSpec S).C.slotOf t } := by
    rw [h0e]
  rw [hst1] at h1
  refine ⟨st0.saved_grades, st2, st3, st4, st5, ?_, ?_, ?_, ?_, rfl⟩
  · rcases h1 with ⟨B, rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inr ⟨B.toProofNamed, on_block_eq_receipt S _ B⟩
    · exact Or.inl rfl
  · rcases h2 with ⟨u, rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inr ⟨u.toProof, on_goldfish_vote_checked_eq_receipt S _ u⟩
    · exact Or.inl rfl
  · rcases h3 with ⟨s', hc⟩ | rfl
    · exact Or.inr ⟨s', hc⟩
    · exact Or.inl rfl
  · rcases h4 with ⟨row, -, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact Or.inr ⟨row.toProofNamed, admit_attestation_eq_receipt S _ row⟩
    · exact Or.inl rfl

omit [Inhabited V] in
/-- The receipt of a Goldfish vote by the member `receipt_process` writes only `gf_votes` and
    `timestamp_vote`. -/
theorem receipt_gfVote_frame (S : Setup V) (st : Spec.Store V) (u : GoldfishVote V) :
    ∃ gv tv, Member.receipt_process S st (.gfVote u) =
      { st with gf_votes := gv, timestamp_vote := tv } :=
  on_goldfish_vote_checked_frame _ _ _

omit [Inhabited V] in
/-- The receipt of an attestation by the member `receipt_process` writes only `attestations` and
    `timestamp_sg_vote`. -/
theorem receipt_attest_frame (S : Setup V) (st : Spec.Store V) (a : NamedAttestation V) :
    ∃ at' ts, Member.receipt_process S st (.attest a) =
      { st with attestations := at', timestamp_sg_vote := ts } :=
  admit_attestation_frame _ _ _

omit [Inhabited V] in
/-- The member `receipt_process` keeps every body. -/
theorem receipt_bodies_subset (S : Setup V) (st : Spec.Store V) (o : NamedObject V) :
    Member.bodies st ⊆ Member.bodies (Member.receipt_process S st o) :=
  Finset.map_subset_map.mpr (keeps_receipt_process S st o).2.2.1

/-- The member `tick` keeps every body. -/
theorem tick_bodies_subset {S : Setup V} {v : V} {n : Spec.NodeState V} {t : Time}
    {out : Spec.NodeState V × List (NamedObject V)}
    (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out) :
    Member.bodies n.st ⊆ Member.bodies out.1.st :=
  tick_store_rel (R := fun a b => Member.bodies a ⊆ Member.bodies b) hout (fun _ => subset_refl _)
    (fun _ _ _ h1 h2 => subset_trans h1 h2) (receipt_bodies_subset S)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact subset_refl _) (fun _ => subset_refl _)
    (fun _ => subset_refl _)

/-- The field `step_bodies_subset` of `NodeFacts` at `Model.specDraftBase`: for every world `w'`
    that the event `e` can lead to from the world `w`, every named block validator `v` holds in `w`
    it also holds in `w'`. -/
theorem specDraftBase_step_bodies_subset : ∀ (S : Setup V) (w : V → (Model.specDraftBase (V := V)).N) (e : Record.Event V) (v : V)
    (w' : V → (Model.specDraftBase (V := V)).N) (hw' : w' ∈ worldStepOf (Model.specDraftBase (V := V)) S w e), (w v).st.bodies ⊆ (w' v).st.bodies := by
  intro S w e v w' hw'
  cases e with
  | wake v' t =>
    have hw'' : w' = Function.update w v' ((Model.specDraftBase (V := V)).wake (w v')) := hw'
    subst hw''
    by_cases hv : v = v'
    · subst hv
      rw [Function.update_self]
      exact subset_refl _
    · rw [Function.update_of_ne hv]
  | tick v' t =>
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = v'
      · subst hv
        rw [Function.update_self]
        exact tick_bodies_subset hout
      · rw [Function.update_of_ne hv]
    · exact subset_refl _
  | deliver v' o t =>
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = v'
      · subst hv
        rw [Function.update_self]
        obtain rfl := (process_returns_iff _ _ _ _).mp hn'
        show Member.bodies (w v).st ⊆ Member.bodies (receiveNamedObject S (w v) o).st
        rw [receiveNamedObject_eq]
        exact receipt_bodies_subset S _ o
      · rw [Function.update_of_ne hv]
    · exact subset_refl _

/-- A world `w'` that the event `e` can lead to from `w` at `Model.specDraft` is, at the values of
    its node states, a world the event can lead to at `Model.specDraftBase` from the values of `w`,
    or it is `w` itself. -/
theorem worldStepOf_specDraft_val {S : Setup V} {w w' : V → (Model.specDraft (V := V)).N} {e : Record.Event V}
    (hw' : w' ∈ worldStepOf (Model.specDraft (V := V)) S w e) :
    (fun u => (w' u).val) ∈ worldStepOf (Model.specDraftBase (V := V)) S (fun u => (w u).val) e ∨ w' = w := by
  cases e with
  | wake v t =>
    have h : w' = Function.update w v ((Model.specDraft (V := V)).wake (w v)) := hw'
    subst h
    refine Or.inl ?_
    show (fun u => (Function.update w v ((Model.specDraft (V := V)).wake (w v)) u).val) =
      Function.update (fun u => (w u).val) v ((Model.specDraftBase (V := V)).wake (w v).val)
    funext u
    by_cases hu : u = v
    · subst hu
      simp only [Function.update_self]
      rfl
    · simp only [Function.update_of_ne hu]
  | tick v t =>
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · refine Or.inl (Or.inl ⟨(out.1.val, out.2), hout, ?_⟩)
      funext u
      by_cases hu : u = v
      · subst hu
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hu]
    · exact Or.inr rfl
  | deliver v o t =>
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · refine Or.inl (Or.inl ⟨n'.val, hn', ?_⟩)
      funext u
      by_cases hu : u = v
      · subst hu
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hu]
    · exact Or.inr rfl

/-- The field `step_bodies_subset` of `NodeFacts` at `Model.specDraft`: for every world `w'` that
    the event `e` can lead to from the world `w`, every named block validator `v` holds in `w` it
    also holds in `w'`. -/
theorem specDraft_step_bodies_subset : ∀ (S : Setup V) (w : V → (Model.specDraft (V := V)).N) (e : Record.Event V) (v : V)
    (w' : V → (Model.specDraft (V := V)).N) (hw' : w' ∈ worldStepOf (Model.specDraft (V := V)) S w e), (w v).st.bodies ⊆ (w' v).st.bodies :=
by
  intro S w e v w' hw'
  rcases worldStepOf_specDraft_val hw' with h | rfl
  · exact specDraftBase_step_bodies_subset S (fun u => (w u).val) e v (fun u => (w' u).val) h
  · exact subset_refl _

/-- The field `namedNodeTick_setupWithGST` of `NodeFacts` at `Model.specDraft`: a node's tick is the
    same at the setup `S` and at `S` with its GST replaced by `g`. -/
theorem specDraft_namedNodeTick_setupWithGST : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (g : ℤ) (hg : 0 ≤ g) (v : V) (n : (Model.specDraft (V := V)).N) (t : ℤ), (Model.specDraft (V := V)).tick (DecoupledConsensusModel.Sts.setupWithGST S g hg) v n t = (Model.specDraft (V := V)).tick S v n t := by
  intro S g hg v n t
  rfl

/-! ## Receipt facts at the subtype -/

/-- The store of a node state that the receipt of `Model.specDraft` returns is the spec's receipt on
    `n`'s store, its saved grades clipped at its finalized block. -/
theorem process_val_st (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V)
    (n' : (Model.specDraft (V := V)).N) (hn' : (Model.specDraft (V := V)).process S n o ⇢ n') :
    n'.val.st = Spec.make_grades_compatible_with_finalized
      (Member.receipt_process S n.val.st o) := by
  rw [(process_returns_iff S n.val n'.val o).mp hn', receiveNamedObject_eq]

omit [Fintype V] [Inhabited V] in
/-- The clip of the saved grades writes no other field. -/
theorem mgc_eq (st : Spec.Store V) :
    Spec.make_grades_compatible_with_finalized st =
      { st with saved_grades :=
          Spec.Protocol.make_saved_grades_compatible_with st.F st.saved_grades } := rfl

omit [Fintype V] [Inhabited V] in
/-- On a store of distinct roots, the chain state at the block standing for a tree block's image is
    the chain state of that tree block. -/
theorem σ_read (st : Spec.Store V) (hd : NoRaise.DistinctRoots st.T)
    {X : Spec.Block V} (hX : X ∈ st.T) :
    st.σ (st.blockOfImage X.toProof) = st.σ X := by
  rw [Spec.Store.blockOfImage_toProof_of_injOn st
    (SubtypeEqualities.injOn_of_distinctRoots hd) hX]

/-- The field `frozen_process_preceq` of `NodeFacts` at `Model.specDraft`: if the finalized block of
    `n`'s store is an ancestor of, or equal to, its justified block, the same holds of every node
    state `n`'s receipt of `o` can return. -/
theorem specDraft_frozen_process_preceq : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (h : Block.Preceq n.st.core.F n.st.core.J)
    (n' : (Model.specDraft (V := V)).N) (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    Block.Preceq n'.st.core.F n'.st.core.J := by
  intro S n o h n' hn'
  show Block.Preceq n'.val.st.F.toProof n'.val.st.J.toProof
  rw [process_val_st S n o n' hn', mgc_eq]
  show Block.Preceq (Member.receipt_process S n.val.st o).F.toProof
    (Member.receipt_process S n.val.st o).J.toProof
  rcases SubtypeEqualities.receipt_cases S n.val.st o with
    ⟨-, -, -, -, hJ, -, hF⟩ | ⟨B, -, -, -, -, -, -, hJ, hF⟩
  · rw [hF, hJ]
    exact h
  · rcases hF with hF | ⟨hF, hFJ⟩
    · rcases hJ with ⟨hJ, -⟩ | ⟨hJ, -, hFJ'⟩
      · rw [hF, hJ]
        exact h
      · rw [hF, hJ]
        unfold DecoupledConsensusModel.Block.Preceq
        exact Spec.Block.toProof_preceq_of_ancestorEq _ _ hFJ'
    · rw [hF]
      unfold DecoupledConsensusModel.Block.Preceq
      exact Spec.Block.toProof_preceq_of_ancestorEq _ _ hFJ

/-- The field `process_proposerOk` of `NodeFacts` at `Model.specDraft`: if every block of `n`'s tree
    is genesis or has its slot's proposer, the same holds of every node state `n`'s receipt of `o`
    can return. -/
theorem specDraft_process_proposerOk : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    (∀ B ∈ n.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)) →
      ∀ B ∈ n'.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot) := by
  intro S n o n' hn' h B hB
  have hB' : B ∈ n'.val.st.T.image Spec.Block.toProof := hB
  rw [process_val_st S n o n' hn', mgc_eq] at hB'
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB'
  have hold : X ∈ n.val.st.T → _ := fun hXT => h X.toProof (Finset.mem_image_of_mem _ hXT)
  change X ∈ (Member.receipt_process S n.val.st o).T at hX
  rcases SubtypeEqualities.receipt_cases S n.val.st o with ⟨hT, -⟩ | ⟨B0, -, hadm, hT, -⟩
  · rw [hT] at hX
    exact hold hX
  · rw [hT] at hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact hold hX
    · rw [Finset.mem_singleton.mp hX]
      right
      obtain ⟨-, -, -, -, hprop, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
      rw [SubtypeEqualities.toProof_proposer?, SubtypeEqualities.toProof_slot, hprop]
      rfl

/-- The field `process_core_bound` of `NodeFacts` at `Model.specDraft`: if every block of `n`'s tree
    has a chain-state height at most `n`'s `h_max`, the same holds of every node state `n`'s receipt
    of `o` can return. -/
theorem specDraft_process_core_bound : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    (∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max) →
      ∀ B ∈ n'.st.core.T, (n'.st.core.σ B).h ≤ n'.st.core.h_max := by
  intro S n o n' hn' h B hB
  have hold : ∀ Y ∈ n.val.st.T, (n.val.st.σ Y).h ≤ n.val.st.h_max := fun Y hY => by
    have := h Y.toProof (Finset.mem_image_of_mem _ hY)
    change (n.val.st.σ (n.val.st.blockOfImage Y.toProof)).h ≤ n.val.st.h_max at this
    rwa [σ_read _ n.property.2.1 hY] at this
  have hB' : B ∈ n'.val.st.T.image Spec.Block.toProof := hB
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB'
  show (n'.val.st.σ (n'.val.st.blockOfImage X.toProof)).h ≤ n'.val.st.h_max
  rw [σ_read _ n'.property.2.1 hX]
  rw [process_val_st S n o n' hn', mgc_eq] at hX ⊢
  change X ∈ (Member.receipt_process S n.val.st o).T at hX
  change ((Member.receipt_process S n.val.st o).σ X).h ≤ (Member.receipt_process S n.val.st o).h_max
  rcases SubtypeEqualities.receipt_cases S n.val.st o with
    ⟨hT, hσ, -, hm, -⟩ | ⟨B0, -, hadm, hT, hσ, -, hm, -⟩
  · rw [hT] at hX
    rw [hσ, hm]
    exact hold X hX
  · rw [hT] at hX
    rw [hσ, hm]
    by_cases hXX : X = Spec.Block.toSpecNamed B0
    · rw [hXX, Function.update_self]
      exact le_max_right _ _
    · rw [Function.update_of_ne hXX]
      have hXT : X ∈ n.val.st.T := by
        rcases Finset.mem_union.mp hX with h' | h'
        · exact h'
        · exact absurd (Finset.mem_singleton.mp h') hXX
      exact le_trans (hold X hXT) (le_max_left _ _)

/-- The field `node_process_h_max_le_succ` of `NodeFacts` at `Model.specDraft`: if every block of
    `n`'s tree has a chain-state height at most `n`'s `h_max`, then every node state `n'` that `n`'s
    receipt of `o` can return has an `h_max` at most `n`'s plus one. -/
theorem specDraft_node_process_h_max_le_succ : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V)
    (hbound : ∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max)
    (n' : (Model.specDraft (V := V)).N) (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    n'.st.core.h_max ≤ n.st.core.h_max + 1 := by
  intro S n o hbound n' hn'
  show n'.val.st.h_max ≤ n.val.st.h_max + 1
  rw [process_val_st S n o n' hn', mgc_eq]
  change (Member.receipt_process S n.val.st o).h_max ≤ n.val.st.h_max + 1
  rcases SubtypeEqualities.receipt_cases S n.val.st o with
    ⟨-, -, -, hm, -⟩ | ⟨B0, -, hadm, -, -, -, hm, -⟩
  · rw [hm]
    exact Nat.le_succ _
  · rw [hm]
    obtain ⟨⟨-, hp⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
    have hpar := hbound _ (Finset.mem_image_of_mem _ hp)
    change (n.val.st.σ (n.val.st.blockOfImage _)).h ≤ n.val.st.h_max at hpar
    rw [σ_read _ n.property.2.1 hp] at hpar
    have hv := SubtypeEqualities.state_transition_h_le_succ (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) (n.val.st.σ (Spec.Block.toSpecNamed B0).parent)
      (Spec.Block.toSpecNamed B0)
    exact max_le (Nat.le_succ _) (le_trans hv (Nat.succ_le_succ hpar))

/-- The field `process_core_justifier` of `NodeFacts` at `Model.specDraft`: if some block of `n`'s
    tree has a chain state whose justification and justification height are the store's own, the
    same holds of every node state `n'` that `n`'s receipt of `o` can return. -/
theorem specDraft_process_core_justifier : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.specDraft (V := V)) S.E S.cfg n.st →
    (∃ D ∈ n.st.core.T, (n.st.core.σ D).J = n.st.core.J ∧ (n.st.core.σ D).h_j = n.st.core.h_j) →
      ∃ D ∈ n'.st.core.T, (n'.st.core.σ D).J = n'.st.core.J ∧
        (n'.st.core.σ D).h_j = n'.st.core.h_j := by
  intro S n o n' hn' _ hD
  obtain ⟨D, hD, hDJ, hDh⟩ := hD
  have hD' : D ∈ n.val.st.T.image Spec.Block.toProof := hD
  obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hD'
  change (n.val.st.σ (n.val.st.blockOfImage Y.toProof)).J.toProof = n.val.st.J.toProof at hDJ
  change (n.val.st.σ (n.val.st.blockOfImage Y.toProof)).h_j = n.val.st.h_j at hDh
  rw [σ_read _ n.property.2.1 hY] at hDJ hDh
  have key : ∀ Z ∈ n'.val.st.T, (n'.val.st.σ Z).J.toProof = n'.val.st.J.toProof →
      (n'.val.st.σ Z).h_j = n'.val.st.h_j →
      ∃ D ∈ n'.st.core.T, (n'.st.core.σ D).J = n'.st.core.J ∧
        (n'.st.core.σ D).h_j = n'.st.core.h_j := by
    intro Z hZ e1 e2
    refine ⟨Z.toProof, Finset.mem_image_of_mem _ hZ, ?_, ?_⟩
    · show (n'.val.st.σ (n'.val.st.blockOfImage Z.toProof)).J.toProof = n'.val.st.J.toProof
      rw [σ_read _ n'.property.2.1 hZ, e1]
    · show (n'.val.st.σ (n'.val.st.blockOfImage Z.toProof)).h_j = n'.val.st.h_j
      rw [σ_read _ n'.property.2.1 hZ, e2]
  have hst := process_val_st S n o n' hn'
  rw [mgc_eq] at hst
  rcases SubtypeEqualities.receipt_cases S n.val.st o with
    ⟨hT, hσ, -, -, hJ, hj, -⟩ | ⟨B0, -, hadm, hT, hσ, -, -, hJ, -⟩
  · refine key Y ?_ ?_ ?_ <;> rw [hst]
    · show Y ∈ (Member.receipt_process S n.val.st o).T
      rw [hT]
      exact hY
    · show ((Member.receipt_process S n.val.st o).σ Y).J.toProof =
        (Member.receipt_process S n.val.st o).J.toProof
      rw [hσ, hJ]
      exact hDJ
    · show ((Member.receipt_process S n.val.st o).σ Y).h_j =
        (Member.receipt_process S n.val.st o).h_j
      rw [hσ, hj]
      exact hDh
  · obtain ⟨⟨hXT, -⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
    have hYX : Y ≠ Spec.Block.toSpecNamed B0 := fun e => hXT (e ▸ hY)
    rcases hJ with ⟨hJ, hj⟩ | ⟨hJ, hj, -⟩
    · refine key Y ?_ ?_ ?_ <;> rw [hst]
      · show Y ∈ (Member.receipt_process S n.val.st o).T
        rw [hT]
        exact Finset.mem_union_left _ hY
      · show ((Member.receipt_process S n.val.st o).σ Y).J.toProof =
          (Member.receipt_process S n.val.st o).J.toProof
        rw [hσ, hJ, Function.update_of_ne hYX]
        exact hDJ
      · show ((Member.receipt_process S n.val.st o).σ Y).h_j =
          (Member.receipt_process S n.val.st o).h_j
        rw [hσ, hj, Function.update_of_ne hYX]
        exact hDh
    · refine key (Spec.Block.toSpecNamed B0) ?_ ?_ ?_ <;> rw [hst]
      · show Spec.Block.toSpecNamed B0 ∈ (Member.receipt_process S n.val.st o).T
        rw [hT]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · show ((Member.receipt_process S n.val.st o).σ (Spec.Block.toSpecNamed B0)).J.toProof =
          (Member.receipt_process S n.val.st o).J.toProof
        rw [hσ, hJ, Function.update_self]
      · show ((Member.receipt_process S n.val.st o).σ (Spec.Block.toSpecNamed B0)).h_j =
          (Member.receipt_process S n.val.st o).h_j
        rw [hσ, hj, Function.update_self]

/-- The field `node_process_body_stamp` of `NodeFacts` at `Model.specDraft`: for every node state
    `n'` that `n`'s receipt of `o` can return, a named block `n'` holds and `n` did not is stamped
    in `n'`'s store at `n`'s clock. -/
theorem specDraft_node_process_body_stamp : ∀ (S' : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S' n o ⇢ n') (B : NamedBlock V)
    (h0 : B ∉ n.st.bodies) (h1 : B ∈ n'.st.bodies),
    n'.st.core.timestamp_block B.erase = some ((n.st.core.t : Int) : Stamp) := by
  intro S n o n' hn' B h0 h1
  have h1' : B ∈ n'.val.st.T.map Spec.Block.toProofNamedEmb := h1
  obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp h1'
  have hXn : X ∉ n.val.st.T := fun h => h0 (Finset.mem_map_of_mem _ h)
  show n'.val.st.toProof.timestamp_block (Spec.Block.toProofNamedEmb X).erase =
    some ((n.val.st.t : Int) : Stamp)
  rw [Spec.Block.coe_toProofNamedEmb, Spec.Block.toProofNamed_erase,
    Spec.Store.toProof_timestamp_block_of_mem _
      (SubtypeEqualities.injOn_of_distinctRoots n'.property.2.1) hX]
  rw [process_val_st S n o n' hn', mgc_eq] at hX ⊢
  change X ∈ (Member.receipt_process S n.val.st o).T at hX
  change (Member.receipt_process S n.val.st o).timestamp_block X = _
  rcases SubtypeEqualities.receipt_cases S n.val.st o with ⟨hT, -⟩ | ⟨B0, -, -, hT, -, hτ, -⟩
  · rw [hT] at hX
    exact absurd hX hXn
  · rw [hT] at hX
    rcases Finset.mem_union.mp hX with h | h
    · exact absurd h hXn
    · rw [Finset.mem_singleton.mp h, hτ, Function.update_self]

omit [Inhabited V] in
/-- The spec's `admit_attestation` keeps every attestation of each round. -/
theorem admit_attestation_sg_pool_mono (C : Spec.Config) (st : Spec.Store V)
    (a : Spec.Attestation V) (r : Round) :
    st.sg_pool r ⊆ (Spec.Protocol.admit_attestation C st a).sg_pool r := by
  rcases StoreSteps.admit_attestation_cases C st a with e | ⟨-, e⟩
  · rw [e]
  · rw [e]
    intro x hx
    show x ∈ (Function.update st.attestations a.round (st.attestations a.round ++ [a]) r).toFinset
    have hx' : x ∈ (st.attestations r).toFinset := hx
    by_cases hr : r = a.round
    · subst hr
      rw [Function.update_self]
      simp only [List.mem_toFinset, List.mem_append] at hx' ⊢
      exact Or.inl hx'
    · rw [Function.update_of_ne hr]
      exact hx'

omit [Inhabited V] in
/-- The spec's `admit_attestations` keeps every attestation of each round. -/
theorem admit_attestations_sg_pool_mono (C : Spec.Config) (r : Round)
    (rows : List (Spec.Attestation V)) :
    ∀ st : Spec.Store V,
      st.sg_pool r ⊆ (Spec.Protocol.admit_attestations C st rows).sg_pool r := by
  induction rows with
  | nil => exact fun st => subset_refl _
  | cons a rows ih =>
      intro st
      have e : Spec.Protocol.admit_attestations C st (a :: rows) =
          Spec.Protocol.admit_attestations C
            (Spec.Protocol.admit_attestation C st a) rows := by
        simp only [Spec.Protocol.admit_attestations, Id.run,
          List.forIn_pure_yield_eq_foldl, List.foldl_cons]
      rw [e]
      exact (admit_attestation_sg_pool_mono C st a r).trans (ih _)

omit [Inhabited V] in
/-- The member `receipt_process` keeps every attestation of each round. -/
theorem receipt_sg_pool_mono (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (r : Round) : st.sg_pool r ⊆ (Member.receipt_process S st o).sg_pool r := by
  cases o with
  | gfVote u =>
    obtain ⟨x, y, e⟩ := SubtypeEqualities.foldl_checked_shape
      (Spec.Provisional.toSpec S.E) [Spec.GoldfishVote.toSpec u] st
    have e' : Member.receipt_process S st (.gfVote u) =
        { st with gf_votes := x, timestamp_vote := y } := e
    rw [e']
    exact subset_refl _
  | attest a => exact admit_attestation_sg_pool_mono _ st _ r
  | block B =>
    show st.sg_pool r ⊆ (Spec.Protocol.on_block _ _ st _).sg_pool r
    rw [Handlers.on_block_eq]
    split
    · have hatt := (admitBlockCore_keeps (Spec.Config.toSpec S.E S.hc S.cfg)
        (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B)).2.2.2.1
      refine subset_trans ?_ (admit_attestations_sg_pool_mono _ r _ _)
      show (st.attestations r).toFinset ⊆ ((Handlers.admitBlockCore _ _ st _).attestations r).toFinset
      rw [hatt]
    · exact subset_refl _

/-- The field `sg_pool_subset_process` of `NodeFacts` at `Model.specDraft`: every node state `n'`
    that `n`'s receipt of `o` can return holds every attestation of round `r` that `n`'s store part
    holds. -/
theorem specDraft_sg_pool_subset_process : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (r : Round) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    (Model.specDraft (V := V)).store_sg_pool n.st.core r ⊆
      (Model.specDraft (V := V)).store_sg_pool n'.st.core r := by
  intro S n o r n' hn'
  show (n.val.st.sg_pool r).image Spec.Attestation.toProof ⊆
    (n'.val.st.sg_pool r).image Spec.Attestation.toProof
  apply Finset.image_subset_image
  rw [process_val_st S n o n' hn', mgc_eq]
  exact receipt_sg_pool_mono S n.val.st o r

/-- The field `committeePools_process` of `NodeFacts` at `Model.specDraft`: if every Goldfish vote
    of slot `k` in `n`'s store part is signed by a member of `S.E.committee k`, for every `k`, the
    same holds of every outcome `n'` of `n`'s receipt of `o`. -/
theorem specDraft_committeePools_process : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (n' : (Model.specDraft (V := V)).N),
    (Model.specDraft (V := V)).process S n o ⇢ n' →
    (∀ (k : Slot) (u : GoldfishVote V), u ∈ n.st.core.gf_votes k → u.val_index ∈ S.E.committee k) →
    ∀ (k : Slot) (u : GoldfishVote V), u ∈ n'.st.core.gf_votes k → u.val_index ∈ S.E.committee k := by
  intro S n o n' hn' h k u hu
  have hr := HandlersRunFacts.specDraft_process_reach S n n' o hn' 0
  have hvic : StoreSteps.VotesInCommittee (Setup.toSpec S).P n.val.st := by
    intro k' u' hu'
    have h' := h k' u'.toProof (by
      show u'.toProof ∈ (n.val.st.gf_votes k').map Spec.GoldfishVote.toProof
      exact List.mem_map_of_mem hu')
    simpa [Setup.toSpec, Spec.Provisional.toSpec_committee] using h'
  have hout' := StoreSteps.reach_induction _
    (fun a b hs hq => StoreSteps.votesInCommittee_step _ _ _ a b hs hq) hr hvic
  obtain ⟨u', rfl⟩ := HandlersFacts.exists_vote u
  have hu' : u' ∈ n'.val.st.gf_votes k := by
    have h2 : u'.toProof ∈ (n'.val.st.gf_votes k).map Spec.GoldfishVote.toProof := hu
    simpa [List.mem_map, Spec.GoldfishVote.toProof_injective.eq_iff] using h2
  have h3 := hout' k u' hu'
  simpa [Setup.toSpec, Spec.Provisional.toSpec_committee] using h3

/-- The member `receipt_process` on a store is one step of the store (`StoreSteps.StoreReach`), at
    every clock time `τ`. -/
theorem receipt_reach (S : Setup V) (st : Spec.Store V) (o : NamedObject V) (τ : Time) :
    StoreSteps.StoreReach (Setup.toSpec S).C (Setup.toSpec S).P τ st
      (Member.receipt_process S st o) := by
  cases o with
  | block B => exact Relation.ReflTransGen.single (StoreSteps.StoreStep.block _ _)
  | gfVote u => exact Relation.ReflTransGen.single (StoreSteps.StoreStep.vote _ _)
  | attest a => exact Relation.ReflTransGen.single (StoreSteps.StoreStep.attest _ _)

/-- The field `rawRelay_process_data` of `NodeFacts` at `Model.specDraft`: if the named store `st`
    is coherent, its clock is at or before `bound`, and every named attestation it holds in its rows
    of a round `k` has round `k` and a receipt stamp at or before `bound`, then the same holds of
    the store the receipt of `o` returns on `st`. -/
theorem specDraft_rawRelay_process_data : ∀ (S : Setup V) (bound : Time)
    (st : (Model.specDraft (V := V)).NS) (o : NamedObject V),
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.specDraft (V := V)) S.E S.cfg st →
    (st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
      a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
        st.core.timestamp_sg_vote ((Model.specDraft (V := V)).sgVote a.erase) = some (stamp : Stamp)) →
    (((Model.specDraft (V := V)).receipt_process S st o).core.t ≤ bound ∧
      ∀ k (a : NamedAttestation V), a ∈ ((Model.specDraft (V := V)).receipt_process S st o).sg_rows k →
        a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
          ((Model.specDraft (V := V)).receipt_process S st o).core.timestamp_sg_vote
            ((Model.specDraft (V := V)).sgVote a.erase) = some (stamp : Stamp)) := by
  intro S bound st o _ hst
  obtain ⟨ht, hrows⟩ := hst
  have hI : StoreSteps.RowsErasuresHeld st.val := fun r b hb =>
    (hrows r b.toProofNamed ((HandlersRunFacts.mem_sg_rows_iff st.val r b).2 hb)).1
  have hB : StoreSteps.StampsBounded bound st.val := by
    refine ⟨ht, fun k a ha => ?_⟩
    obtain ⟨-, s, hs, hst⟩ := hrows k a.toProofNamed ((HandlersRunFacts.mem_sg_rows_iff st.val k a).2 ha)
    exact ⟨s, hs, by rwa [HandlersRunFacts.stamp_sgVote_toProofNamed_erase_ok] at hst⟩
  have hreach : StoreSteps.StoreReach (Setup.toSpec S).C (Setup.toSpec S).P bound st.val
      (OkMember.receipt_process S st o).val := by
    by_cases hheld : objectRootHeldByOther st.val.T o
    · rw [OkMember.receipt_process_of_held hheld]
    · rw [OkMember.receipt_process_val_of_not_held hheld]
      exact receipt_reach S st.val o bound
  obtain ⟨hI', hB'⟩ := StoreSteps.reach_bounded bound le_rfl hreach hI hB
  refine ⟨hB'.1, fun k a ha => ?_⟩
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have ha' := (HandlersRunFacts.mem_sg_rows_iff (OkMember.receipt_process S st o).val k a').1 ha
  refine ⟨hI' k a' ha', ?_⟩
  obtain ⟨s, hs, hst'⟩ := hB'.2 k a' ha'
  refine ⟨s, hs, ?_⟩
  rw [HandlersRunFacts.stamp_sgVote_toProofNamed_erase_ok]
  exact hst'

/-! ## Tick facts at the subtype -/

/-- The member `receipt_process` on an object other than a block keeps the tree, the chain states,
    the block stamps, `h_max`, the justified block and height and the finalized block. -/
theorem receipt_keeps_of_not_block (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (ho : ∀ B, o ≠ .block B) :
    (Member.receipt_process S st o).T = st.T ∧ (Member.receipt_process S st o).σ = st.σ ∧
      (Member.receipt_process S st o).timestamp_block = st.timestamp_block ∧
      (Member.receipt_process S st o).h_max = st.h_max ∧
      (Member.receipt_process S st o).J = st.J ∧ (Member.receipt_process S st o).h_j = st.h_j ∧
      (Member.receipt_process S st o).F = st.F := by
  rcases SubtypeEqualities.receipt_cases S st o with h | ⟨B, hB, -⟩
  · exact h
  · exact absurd hB (ho B)

/-- The member `receipt_process` keeps every tree block's chain state at height at most `h_max`. -/
theorem bound_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (h : ∀ X ∈ st.T, (st.σ X).h ≤ st.h_max) :
    ∀ X ∈ (Member.receipt_process S st o).T,
      ((Member.receipt_process S st o).σ X).h ≤ (Member.receipt_process S st o).h_max := by
  intro X hX
  rcases SubtypeEqualities.receipt_cases S st o with
    ⟨hT, hσ, -, hm, -⟩ | ⟨B0, -, -, hT, hσ, -, hm, -⟩
  · rw [hT] at hX
    rw [hσ, hm]
    exact h X hX
  · rw [hT] at hX
    rw [hσ, hm]
    by_cases hXX : X = Spec.Block.toSpecNamed B0
    · rw [hXX, Function.update_self]
      exact le_max_right _ _
    · rw [Function.update_of_ne hXX]
      have hXT : X ∈ st.T := by
        rcases Finset.mem_union.mp hX with h' | h'
        · exact h'
        · exact absurd (Finset.mem_singleton.mp h') hXX
      exact le_trans (h X hXT) (le_max_left _ _)

/-- The member `receipt_process` raises `h_max` by at most one when every tree block's chain state
    has height at most `h_max`. -/
theorem h_max_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (h : ∀ X ∈ st.T, (st.σ X).h ≤ st.h_max) :
    (Member.receipt_process S st o).h_max ≤ st.h_max + 1 := by
  rcases SubtypeEqualities.receipt_cases S st o with
    ⟨-, -, -, hm, -⟩ | ⟨B0, -, hadm, -, -, -, hm, -⟩
  · rw [hm]
    exact Nat.le_succ _
  · rw [hm]
    obtain ⟨⟨-, hp⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
    have hv := SubtypeEqualities.state_transition_h_le_succ
      (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E)
      (st.σ (Spec.Block.toSpecNamed B0).parent) (Spec.Block.toSpecNamed B0)
    exact max_le (Nat.le_succ _) (le_trans hv (Nat.succ_le_succ (h _ hp)))

/-- The member `receipt_process` keeps a tree block whose chain state carries the store's
    justification. -/
theorem justifier_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (h : ∃ X ∈ st.T, (st.σ X).J.toProof = st.J.toProof ∧ (st.σ X).h_j = st.h_j) :
    ∃ X ∈ (Member.receipt_process S st o).T,
      ((Member.receipt_process S st o).σ X).J.toProof = (Member.receipt_process S st o).J.toProof ∧
        ((Member.receipt_process S st o).σ X).h_j = (Member.receipt_process S st o).h_j := by
  obtain ⟨Y, hY, hYJ, hYh⟩ := h
  rcases SubtypeEqualities.receipt_cases S st o with
    ⟨hT, hσ, -, -, hJ, hj, -⟩ | ⟨B0, -, hadm, hT, hσ, -, -, hJ, -⟩
  · refine ⟨Y, hT ▸ hY, ?_, ?_⟩
    · rw [hσ, hJ]
      exact hYJ
    · rw [hσ, hj]
      exact hYh
  · obtain ⟨⟨hXT, -⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
    have hYX : Y ≠ Spec.Block.toSpecNamed B0 := fun e => hXT (e ▸ hY)
    rcases hJ with ⟨hJ, hj⟩ | ⟨hJ, hj, -⟩
    · refine ⟨Y, ?_, ?_, ?_⟩
      · rw [hT]
        exact Finset.mem_union_left _ hY
      · rw [hσ, hJ, Function.update_of_ne hYX]
        exact hYJ
      · rw [hσ, hj, Function.update_of_ne hYX]
        exact hYh
    · refine ⟨Spec.Block.toSpecNamed B0, ?_, ?_, ?_⟩
      · rw [hT]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · rw [hσ, hJ, Function.update_self]
      · rw [hσ, hj, Function.update_self]

/-- The member `receipt_process` keeps the image of the finalized block an ancestor of, or equal to,
    the image of the justified block. -/
theorem frozen_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (h : Block.Preceq st.F.toProof st.J.toProof) :
    Block.Preceq (Member.receipt_process S st o).F.toProof
      (Member.receipt_process S st o).J.toProof := by
  rcases SubtypeEqualities.receipt_cases S st o with
    ⟨-, -, -, -, hJ, -, hF⟩ | ⟨B, -, -, -, -, -, -, hJ, hF⟩
  · rw [hF, hJ]
    exact h
  · rcases hF with hF | ⟨hF, hFJ⟩
    · rcases hJ with ⟨hJ, -⟩ | ⟨hJ, -, hFJ'⟩
      · rw [hF, hJ]
        exact h
      · rw [hF, hJ]
        unfold DecoupledConsensusModel.Block.Preceq
        exact Spec.Block.toProof_preceq_of_ancestorEq _ _ hFJ'
    · rw [hF]
      unfold DecoupledConsensusModel.Block.Preceq
      exact Spec.Block.toProof_preceq_of_ancestorEq _ _ hFJ

/-- The member `receipt_process` keeps every image of a tree block genesis or of its slot's
    proposer. -/
theorem proposerOk_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (h : ∀ B ∈ st.T.image Spec.Block.toProof,
      B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)) :
    ∀ B ∈ (Member.receipt_process S st o).T.image Spec.Block.toProof,
      B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot) := by
  intro B hB
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB
  have hold : X ∈ st.T → _ := fun hXT => h X.toProof (Finset.mem_image_of_mem _ hXT)
  rcases SubtypeEqualities.receipt_cases S st o with ⟨hT, -⟩ | ⟨B0, -, hadm, hT, -⟩
  · rw [hT] at hX
    exact hold hX
  · rw [hT] at hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact hold hX
    · rw [Finset.mem_singleton.mp hX]
      right
      obtain ⟨-, -, -, -, hprop, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
      rw [SubtypeEqualities.toProof_proposer?, SubtypeEqualities.toProof_slot, hprop]
      rfl

omit [Fintype V] [Inhabited V] in
/-- On a store of distinct roots, the height bound read through the images is the bound read on the
    tree. -/
theorem bound_iff (st : Spec.Store V) (hd : NoRaise.DistinctRoots st.T) :
    (∀ B ∈ st.T.image Spec.Block.toProof, (st.σ (st.blockOfImage B)).h ≤ st.h_max) ↔
      ∀ X ∈ st.T, (st.σ X).h ≤ st.h_max := by
  constructor
  · intro h X hX
    have := h X.toProof (Finset.mem_image_of_mem _ hX)
    rwa [σ_read _ hd hX] at this
  · intro h B hB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB
    rw [σ_read _ hd hX]
    exact h X hX

omit [Fintype V] [Inhabited V] in
/-- On a store of distinct roots, a tree block carrying the store's justification exists read
    through the images exactly when one exists read on the tree. -/
theorem justifier_iff (st : Spec.Store V) (hd : NoRaise.DistinctRoots st.T) :
    (∃ D ∈ st.T.image Spec.Block.toProof,
        (st.σ (st.blockOfImage D)).J.toProof = st.J.toProof ∧ (st.σ (st.blockOfImage D)).h_j = st.h_j) ↔
      ∃ X ∈ st.T, (st.σ X).J.toProof = st.J.toProof ∧ (st.σ X).h_j = st.h_j := by
  constructor
  · rintro ⟨D, hD, h1, h2⟩
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hD
    rw [σ_read _ hd hX] at h1 h2
    exact ⟨X, hX, h1, h2⟩
  · rintro ⟨X, hX, h1, h2⟩
    refine ⟨X.toProof, Finset.mem_image_of_mem _ hX, ?_, ?_⟩ <;> rw [σ_read _ hd hX]
    · exact h1
    · exact h2

/-- The field `tick_core_bound` of `NodeFacts` at `Model.specDraft`: if every block of `n`'s tree
    has a chain-state height at most `n`'s `h_max`, the same holds of the store of every outcome
    `out` of `v`'s tick at `t` from `n`. -/
theorem specDraft_tick_core_bound : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N)
    (t : Time) (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    (∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max) →
      ∀ B ∈ out.1.st.core.T, (out.1.st.core.σ B).h ≤ out.1.st.core.h_max := by
  intro S v n t out hout h
  have hfin := tick_store_rel (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
    (fun a b => (∀ X ∈ a.T, (a.σ X).h ≤ a.h_max) → ∀ X ∈ b.T, (b.σ X).h ≤ b.h_max)
    (fun _ => id) (fun _ _ _ h1 h2 => h2 ∘ h1) (fun st o => bound_receipt S st o)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact id) (fun _ => id) (fun _ => id)
    ((bound_iff n.val.st n.property.2.1).mp h)
  exact (bound_iff out.1.val.st out.1.property.2.1).mpr hfin

/-- The field `tick_proposerOk` of `NodeFacts` at `Model.specDraft`: if every block of `n`'s tree is
    genesis or was proposed by its slot's proposer, the same holds of the store of every outcome
    `out` of `v`'s tick at `t` from `n`. -/
theorem specDraft_tick_proposerOk : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N)
    (t : Time) (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    (∀ B ∈ n.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)) →
      ∀ B ∈ out.1.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot) := by
  intro S v n t out hout h
  exact tick_store_rel (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
    (fun a b => (∀ B ∈ a.T.image Spec.Block.toProof,
        B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)) →
      ∀ B ∈ b.T.image Spec.Block.toProof,
        B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot))
    (fun _ => id) (fun _ _ _ h1 h2 => h2 ∘ h1) (fun st o => proposerOk_receipt S st o)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact id) (fun _ => id) (fun _ => id) h

/-- The field `sg_pool_subset_on_tick_emit` of `NodeFacts` at `Model.specDraft`: the store of every
    outcome `out` of `v`'s tick at `t` from `n` holds every attestation of round `r` that `n`'s
    store part holds. -/
theorem specDraft_sg_pool_subset_on_tick_emit : ∀ (S : Setup V) (v : V)
    (n : (Model.specDraft (V := V)).N) (t : Time) (r : Round)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    (Model.specDraft (V := V)).store_sg_pool n.st.core r ⊆
      (Model.specDraft (V := V)).store_sg_pool out.1.st.core r := by
  intro S v n t r out hout
  show (n.val.st.sg_pool r).image Spec.Attestation.toProof ⊆
    (out.1.val.st.sg_pool r).image Spec.Attestation.toProof
  apply Finset.image_subset_image
  exact tick_store_rel (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
    (fun a b => a.sg_pool r ⊆ b.sg_pool r) (fun _ => subset_refl _)
    (fun _ _ _ h1 h2 => subset_trans h1 h2) (fun st o => receipt_sg_pool_mono S st o r)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact subset_refl _)
    (fun _ => subset_refl _) (fun _ => subset_refl _)

/-- The field `frozen_tick_preceq` of `NodeFacts` at `Model.specDraft`: if the finalized block of
    `n`'s store is an ancestor of, or equal to, its justified block, the same holds of the store of
    every outcome `out` of `v`'s tick at `t` from `n`. -/
theorem specDraft_frozen_tick_preceq : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N)
    (t : Time) (h : Block.Preceq n.st.core.F n.st.core.J)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    Block.Preceq out.1.st.core.F out.1.st.core.J := by
  intro S v n t h out hout
  exact tick_store_rel (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
    (fun a b => Block.Preceq a.F.toProof a.J.toProof → Block.Preceq b.F.toProof b.J.toProof)
    (fun _ => id) (fun _ _ _ h1 h2 => h2 ∘ h1) (fun st o => frozen_receipt S st o)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact id) (fun _ => id) (fun _ => id) h

/-- The field `tick_core_justifier` of `NodeFacts` at `Model.specDraft`: if some block of `n`'s tree
    has a chain state whose justification and justification height are the store's own, the same
    holds of the store of every outcome `out` of `v`'s tick at `t` from `n`. -/
theorem specDraft_tick_core_justifier : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N)
    (t : Time) (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.specDraft (V := V)) S.E S.cfg n.st →
    (∃ D ∈ n.st.core.T, (n.st.core.σ D).J = n.st.core.J ∧ (n.st.core.σ D).h_j = n.st.core.h_j) →
      ∃ D ∈ out.1.st.core.T, (out.1.st.core.σ D).J = out.1.st.core.J ∧
        (out.1.st.core.σ D).h_j = out.1.st.core.h_j := by
  intro S v n t out hout _ h
  have hfin := tick_store_rel (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
    (fun a b => (∃ X ∈ a.T, (a.σ X).J.toProof = a.J.toProof ∧ (a.σ X).h_j = a.h_j) →
      ∃ X ∈ b.T, (b.σ X).J.toProof = b.J.toProof ∧ (b.σ X).h_j = b.h_j)
    (fun _ => id) (fun _ _ _ h1 h2 => h2 ∘ h1) (fun st o => justifier_receipt S st o)
    (fun st s st' hc => by rw [update_confirmation_ok hc]; exact id) (fun _ => id) (fun _ => id)
    ((justifier_iff n.val.st n.property.2.1).mp h)
  exact (justifier_iff out.1.val.st out.1.property.2.1).mpr hfin

/-- The field `node_tick_h_max_le_succ` of `NodeFacts` at `Model.specDraft`: if every block of `n`'s
    tree has a chain-state height at most `n`'s `h_max`, then the store of every outcome `out` of
    `v`'s tick at `t` from `n` has an `h_max` at most `n`'s plus one. -/
theorem specDraft_node_tick_h_max_le_succ : ∀ (S : Setup V) (v : V)
    (n : (Model.specDraft (V := V)).N) (t : Time)
    (hbound : ∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    out.1.st.core.h_max ≤ n.st.core.h_max + 1 := by
  intro S v n t hbound out hout
  have h' := (bound_iff n.val.st n.property.2.1).mp hbound
  obtain ⟨sg, st2, st3, st4, st5, e1, e2, e3, e4, hst⟩ :=
    tick_chain (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
  show out.1.val.st.h_max ≤ n.val.st.h_max + 1
  rw [hst, mgc_eq]
  change st5.h_max ≤ n.val.st.h_max + 1
  have k5 : st5.h_max = st4.h_max := by
    rcases e4 with rfl | ⟨a, rfl⟩
    · rfl
    · exact (receipt_keeps_of_not_block S st4 _ (fun B h => by cases h)).2.2.2.1
  have k4 : st4.h_max = st3.h_max := by
    rcases e3 with rfl | ⟨s, hc⟩
    · rfl
    · rw [update_confirmation_ok hc]
  have k3 : st3.h_max = st2.h_max := by
    rcases e2 with rfl | ⟨u, rfl⟩
    · rfl
    · exact (receipt_keeps_of_not_block S st2 _ (fun B h => by cases h)).2.2.2.1
  rw [k5, k4, k3]
  rcases e1 with rfl | ⟨B, rfl⟩
  · exact Nat.le_succ _
  · exact h_max_receipt S _ (.block B) h'

/-- The field `node_tick_body_stamp` of `NodeFacts` at `Model.specDraft`: for every outcome `out` of
    `v`'s tick at `t` from `n`, a named block `out.1` holds and `n` did not is stamped in `out.1`'s
    store at `t`. -/
theorem specDraft_node_tick_body_stamp : ∀ (S' : Setup V) (v : V)
    (n : (Model.specDraft (V := V)).N) (t : Int)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S' v n t ⇢ out) (B : NamedBlock V)
    (h0 : B ∉ n.st.bodies) (h1 : B ∈ out.1.st.bodies),
    out.1.st.core.timestamp_block B.erase = some (t : Stamp) := by
  intro S v n t out hout B h0 h1
  obtain ⟨sg, st2, st3, st4, st5, e1, e2, e3, e4, hst⟩ :=
    tick_chain (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout
  have h1' : B ∈ out.1.val.st.T.map Spec.Block.toProofNamedEmb := h1
  obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp h1'
  have hXn : X ∉ n.val.st.T := fun h => h0 (Finset.mem_map_of_mem _ h)
  show out.1.val.st.toProof.timestamp_block (Spec.Block.toProofNamedEmb X).erase =
    some (t : Stamp)
  rw [Spec.Block.coe_toProofNamedEmb, Spec.Block.toProofNamed_erase,
    Spec.Store.toProof_timestamp_block_of_mem _
      (SubtypeEqualities.injOn_of_distinctRoots out.1.property.2.1) hX]
  rw [hst, mgc_eq] at hX ⊢
  change X ∈ st5.T at hX
  change st5.timestamp_block X = _
  have k5 : st5.T = st4.T ∧ st5.timestamp_block = st4.timestamp_block := by
    rcases e4 with rfl | ⟨a, rfl⟩
    · exact ⟨rfl, rfl⟩
    · obtain ⟨k1, -, k2, -⟩ := receipt_keeps_of_not_block S st4 (.attest a) (fun B h => by cases h)
      exact ⟨k1, k2⟩
  have k4 : st4.T = st3.T ∧ st4.timestamp_block = st3.timestamp_block := by
    rcases e3 with rfl | ⟨s, hc⟩
    · exact ⟨rfl, rfl⟩
    · rw [update_confirmation_ok hc]
      exact ⟨rfl, rfl⟩
  have k3 : st3.T = st2.T ∧ st3.timestamp_block = st2.timestamp_block := by
    rcases e2 with rfl | ⟨u, rfl⟩
    · exact ⟨rfl, rfl⟩
    · obtain ⟨k1, -, k2, -⟩ := receipt_keeps_of_not_block S st2 (.gfVote u) (fun B h => by cases h)
      exact ⟨k1, k2⟩
  rw [k5.1, k4.1, k3.1] at hX
  rw [k5.2, k4.2, k3.2]
  rcases e1 with rfl | ⟨B0, rfl⟩
  · exact absurd hX hXn
  · rcases SubtypeEqualities.receipt_cases S _ (.block B0) with
      ⟨hT, -⟩ | ⟨B1, -, -, hT, -, hτ, -⟩
    · rw [hT] at hX
      exact absurd hX hXn
    · rw [hT] at hX
      rcases Finset.mem_union.mp hX with h | h
      · exact absurd h hXn
      · rw [Finset.mem_singleton.mp h, hτ, Function.update_self]

/-! ## The cache facts at the subtype -/

/-- The field `cache_clipped_process` of `NodeFacts` at `Model.specDraftBase`: for every node state
    `n'` that `n`'s receipt of `o` can return, `n'`'s grade cache clipped at the finalized block of
    its store is that cache. -/
theorem specDraftBase_cache_clipped_process : ∀ (S : Setup V)
    (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V)
    (n' : (Model.specDraftBase (V := V)).N) (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'),
    (Model.specDraftBase (V := V)).clipCache n'.st.core.F n'.cache = n'.cache := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  exact SubtypeEqualities.clipCache_make_saved_grades_compatible_with _ _

/-- The field `cache_clipped_process` of `NodeFacts` at `Model.specDraft`: for every node state `n'`
    that `n`'s receipt of `o` can return, `n'`'s grade cache clipped at the finalized block of its
    store is that cache. -/
theorem specDraft_cache_clipped_process : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'),
    (Model.specDraft (V := V)).clipCache n'.st.core.F n'.cache = n'.cache :=
  fun S n o n' hn' => specDraftBase_cache_clipped_process S n.val o n'.val hn'

/-- The field `cache_clipped_tick` of `NodeFacts` at `Model.specDraftBase`: for every outcome `out`
    of `v`'s tick at `t` from `n`, `out.1`'s grade cache clipped at the finalized block of its store
    is that cache. -/
theorem specDraftBase_cache_clipped_tick : ∀ (S : Setup V) (v : V)
    (n : (Model.specDraftBase (V := V)).N) (t : Time)
    (out : (Model.specDraftBase (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraftBase (V := V)).tick S v n t ⇢ out),
    (Model.specDraftBase (V := V)).clipCache out.1.st.core.F out.1.cache = out.1.cache := by
  intro S v n t out hout
  obtain ⟨sg, st5, -, hst, -, -⟩ := tick_store hout
  show Member.clipCache (Spec.NodeState.st out.1).F.toProof
      (Spec.NodeState.st out.1).saved_grades =
    (Spec.NodeState.st out.1).saved_grades
  rw [hst]
  exact SubtypeEqualities.clipCache_make_saved_grades_compatible_with _ _

/-- The field `cache_clipped_tick` of `NodeFacts` at `Model.specDraft`: for every outcome `out` of
    `v`'s tick at `t` from `n`, `out.1`'s grade cache clipped at the finalized block of its store is
    that cache. -/
theorem specDraft_cache_clipped_tick : ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N)
    (t : Time) (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out),
    (Model.specDraft (V := V)).clipCache out.1.st.core.F out.1.cache = out.1.cache :=
  fun S v n t out hout => specDraftBase_cache_clipped_tick S v n.val t (out.1.val, out.2) hout

end SpecDraftRecord.NodeFacts

namespace SpecDraftRecord.NodeRunFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NodeFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `process_live_confirmed` of `NodeRunFacts` at `Model.specDraftBase`: every node state
    `n'` that `n`'s receipt of `o` can return has the `live_confirmed` of `n`'s store. -/
theorem specDraftBase_process_live_confirmed : ∀ (S : Setup V) (n : (Model.specDraftBase (V := V)).N) (o : NamedObject V) (n' : (Model.specDraftBase (V := V)).N)
    (hn' : (Model.specDraftBase (V := V)).process S n o ⇢ n'), n'.st.core.live_confirmed = n.st.core.live_confirmed := by
  intro S n o n' hn'
  obtain rfl := (process_returns_iff S n n' o).mp hn'
  rw [receiveNamedObject_eq]
  show (Member.receipt_process S n.st o).live_confirmed.toProof = n.st.live_confirmed.toProof
  rw [(keeps_receipt_process S n.st o).2.2.2.2.2.1]

/-- The field `process_live_confirmed` of `NodeRunFacts` at `Model.specDraft`: every node state `n'`
    that `n`'s receipt of `o` can return has the `live_confirmed` of `n`'s store. -/
theorem specDraft_process_live_confirmed : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
    (hn' : (Model.specDraft (V := V)).process S n o ⇢ n'), n'.st.core.live_confirmed = n.st.core.live_confirmed :=
  fun S n o n' hn' => specDraftBase_process_live_confirmed S n.val o n'.val hn'

/-- The field `stateBefore_zero_body_eq_genesis` of `NodeRunFacts` at `Model.specDraft`: for every
    world `w` that the run `rho` can reach before its first event, every body that `v` holds in `w`
    is genesis. -/
theorem specDraft_stateBefore_zero_body_eq_genesis : ∀ (S : Setup V) (rho : Record.Run V) (v : V) (w : V → (Model.specDraft (V := V)).N)
    (hw : w ∈ stateBeforeOf (Model.specDraft (V := V)) S rho 0) {D : NamedBlock V} (hD : D ∈ (w v).st.bodies),
    D = NamedBlock.genesis := by
  intro S rho v w hw D hD
  have hw' : w = fun u => (Model.specDraft (V := V)).initial S u := hw
  subst hw'
  exact specDraft_initial_body_eq_genesis S v hD

end SpecDraftRecord.NodeRunFacts

