import Proofs.Instance.Facts.GradesRun
import Proofs.Instance.Facts.Duties
import Proofs.Instance.Facts.HandlersStore
import Proofs.Instance.Facts.NonEmpty
import Proofs.Instance.Equalities.ContractImages

/-!
# Duty facts at reached stores of `Model.spec`

Fields of `DutiesFacts`, `NodeFacts` and `HandlersFacts` at `Model.spec` that hold at a store a
run reaches. There, reading the store through its tree is the identity, and a duty's store is the
store that received the object the duty sent, with the contract written in.
-/

set_option autoImplicit false

namespace SpecRecord.DutiesReached

open Spec
open scoped DC

variable {V : Type} [DecidableEq V]

/-- A store with the run invariant reads as itself through its tree. -/
theorem ofImage_eq_of_inv {st : OkStore V}
    (hinv : SubtypeEqualities.RunStoreInv st.val) (hconf : HandlersRunFacts.ConfirmedInTree st.val) :
    Store.ofImage st.val = st.val :=
  Store.ofImage_eq_self _ st.property.2.1 st.property.2.2.2 hinv.1 hconf.1 hconf.2.1 hconf.2.2

/-- When another tree block has `B`'s root, `on_block` of `B` keeps the store, provided the store it
    returns has distinct roots. -/
theorem on_block_of_rootHeld [Fintype V] (C : Config) (P : Provisional V) (st : Store V)
    (B : Block V) (hr : RootHeldByOther st.T B)
    (hd : NoRaise.DistinctRoots (Protocol.on_block C P st B).T) :
    Protocol.on_block C P st B = st := by
  obtain ⟨Y, hY, hne, hroot⟩ := hr
  rw [Handlers.on_block_eq] at hd ⊢
  by_cases hadm : Protocol.block_admissible C P st B = true
  · exfalso
    rw [if_pos hadm] at hd
    have hcore : Handlers.admitBlockCore C P st B = Handlers.blockCore C P st B := if_pos hadm
    rw [hcore] at hd
    have hX : B ∈ (Protocol.admit_attestations C (Handlers.blockCore C P st B) B.attestations).T :=
      (NodeFacts.keeps_admit_attestations _ _ _).2.2.1 (NodeFacts.blockCore_keeps _ _ _ _).2.2
    have hY' : Y ∈ (Protocol.admit_attestations C (Handlers.blockCore C P st B) B.attestations).T :=
      (NodeFacts.keeps_admit_attestations _ _ _).2.2.1 ((NodeFacts.blockCore_keeps _ _ _ _).1.2.2.1 hY)
    exact hne (hd Y hY' B hX hroot)
  · rw [if_neg hadm]

/-- An answer of the Goldfish vote duty either sends a vote `u` and returns the store after
    `on_goldfish_vote_checked` of `u`, or sends nothing and returns the store. -/
theorem goldfish_vote_out [Fintype V] {C : Config} {P : Provisional V} {v : V} {st : Store V}
    {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (Protocol.goldfish_vote C P v st).run l = .ok out) :
    (∃ u, out.2 = l ++ [NamedObject.gfVote u] ∧ out.1 = Protocol.on_goldfish_vote_checked P st u) ∨
      (out.2 = l ∧ out.1 = st) := by
  unfold Protocol.goldfish_vote at h
  dsimp only at h
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨_, l1, h1, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h1
  obtain ⟨-, rfl⟩ := h1
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨_, l2, h2, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h2
  obtain ⟨-, rfl⟩ := h2
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨_, l3, h3, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h3
  obtain ⟨-, rfl⟩ := h3
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨H, l4, h4, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h4
  obtain ⟨-, rfl⟩ := h4
  split_ifs at h with hv
  · rw [NoRaise.DREB.run_bind_ok_iff] at h
    obtain ⟨_, l5, h5, h⟩ := h
    rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    have e5 := Except.ok.inj h5
    simp only [Prod.mk.injEq, true_and] at e5
    subst e5
    exact Or.inl ⟨_, rfl, rfl⟩
  · rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    exact Or.inr ⟨rfl, rfl⟩

end SpecRecord.DutiesReached

namespace SpecRecord.DutiesReached

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecRecord.ContractImages
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At a store with the run invariant, an outcome of the proposal duty sends the block `B'` the spec
    builds and returns the spec's `on_block` of `B'` on the store, with the contract as saved
    grades. -/
theorem propose_out {contract : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig} {nd : Protocol.Node V}
    {st : OkStore V} (hinv : SubtypeEqualities.RunStoreInv st.val)
    (hconf : HandlersRunFacts.ConfirmedInTree st.val)
    {D : (Model.spec (V := V)).NS × Option (NamedBlock V)}
    (hD : (Model.spec (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D) :
    ∃ B' : Spec.Block V, D.2 = some B'.toProofNamed ∧
      D.1.val = { Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
        (Spec.Provisional.toSpec E) st.val B' with saved_grades := contract } := by
  obtain ⟨B', -, hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  refine ⟨B', congrArg (fun x => x.2) hD', ?_⟩
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  rw [h1, on_block_with_saved_grades, ofImage_eq_of_inv hinv hconf]

/-- The receipt member `on_block_with` is the spec's `on_block` of the block, with `st`'s saved
    grades written back, when the result keeps the roots distinct. -/
theorem on_block_with_val {E : Env V} {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig}
    (st : OkStore V) (B' : Spec.Block V)
    (hd : NoRaise.DistinctRoots (Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
        (Spec.Provisional.toSpec E) st.val B').T) :
    ((Model.spec (V := V)).on_block_with .alsoCarried E hc cfg st B'.toProofNamed).val =
      Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
        (Spec.Provisional.toSpec E) st.val B' := by
  show (OkMember.on_block_with .alsoCarried E hc cfg st B'.toProofNamed).val = _
  unfold OkMember.on_block_with
  by_cases hr : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B'.toProofNamed)
  · rw [dif_pos hr]
    rw [Spec.Block.toSpecNamed_toProofNamed] at hr
    rw [on_block_of_rootHeld _ _ _ _ hr hd]
  · rw [dif_neg hr]
    show Spec.Protocol.on_block _ _ st.val
      (Spec.Block.toSpecNamed B'.toProofNamed) = _
    rw [Spec.Block.toSpecNamed_toProofNamed]

/-- At a store with the run invariant, the attestation duty admits the attestation it builds into
    the store, writes the contract in as saved grades, and sends that attestation. -/
theorem attest_out {contract : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : OkStore V}
    (hinv : SubtypeEqualities.RunStoreInv st.val)
    (hconf : HandlersRunFacts.ConfirmedInTree st.val) {record : Spec.SigningHistory}
    {D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V}
    (hD : (Model.spec (V := V)).duties_attest_with contract E hc nd st record ⇢ D) :
    ∃ p, Spec.Protocol.build_attestation (Spec.Config.toSpec E hc unreadHeightConfig)
        nd.val_index { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.val.contractOfImage contract) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) }
        record = .ok p ∧
      D.1.val = { Spec.Protocol.admit_attestation
        (Spec.Config.toSpec E hc unreadHeightConfig) st.val p.2 with saved_grades := contract } ∧
      D.2 = (p.1, p.2.toProofNamed) := by
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  refine ⟨p, hp, ?_, congrArg (fun x => x.2) hD'⟩
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  rw [h1, admit_attestation_with_saved_grades, ofImage_eq_of_inv hinv hconf]

/-- At a store with the run invariant, the Goldfish vote duty admits the vote it sends, if any, and
    writes the contract in as saved grades. -/
theorem vote_out {contract : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : OkStore V}
    (hinv : SubtypeEqualities.RunStoreInv st.val)
    (hconf : HandlersRunFacts.ConfirmedInTree st.val)
    {D : (Model.spec (V := V)).NS × Option (GoldfishVote V)}
    (hD : (Model.spec (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D) :
    (∃ u : Spec.GoldfishVote V, D.2 = some u.toProof ∧
      D.1.val = { Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec E)
        st.val u with saved_grades := contract }) ∨
      (D.2 = none ∧ D.1.val = { st.val with saved_grades := contract }) := by
  have h := (returns_preimageOutcomes _ _ _).1 hD
  unfold Member.duties_goldfish_vote_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, e⟩ := except_map_eq_ok h
  have e1 : D.1.val = { out.1 with saved_grades := contract } := (congrArg (fun x => x.1) e).symm
  have e2 : D.2 = (Member.firstSentGoldfishVote out.2).map Spec.GoldfishVote.toProof :=
    (congrArg (fun x => x.2) e).symm
  rcases goldfish_vote_out hout with ⟨u, hl, hs⟩ | ⟨hl, hs⟩
  · refine Or.inl ⟨u, ?_, ?_⟩
    · rw [e2, hl]
      rfl
    · rw [e1, hs, on_goldfish_vote_checked_with_saved_grades, ofImage_eq_of_inv hinv hconf]
  · refine Or.inr ⟨?_, ?_⟩
    · rw [e2, hl]
      rfl
    · rw [e1, hs, ofImage_eq_of_inv hinv hconf]

end SpecRecord.DutiesReached

namespace DecoupledConsensusModel.Sts.Record

open SpecRecord

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (Record)
open Internal
open Execution
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedActions
open Protocol.NamedActions
open DecoupledConsensusModel.Proofs.NamedDuties
open Protocol.NamedDuties
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (HealConfig)
open Internal.NamedRecoveryRead
open Protocol
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)

/-- At `Model.spec`, if the proposal duty at a reached store `st` sends `B`, its outcome is the
    store that received `B` with the contract's cache written in, and `B`. -/
theorem _root_.SpecRecord.DutiesFacts.spec_propose_block_with_eq_of_snd :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) {B : NamedBlock V}
      (D : (Model.spec (V := V)).NS × Option (NamedBlock V)) (hD : (Model.spec (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D)
      (h : D.2 = some B) (hn : (Model.spec (V := V)).reachedStore st), D = ((Model.spec (V := V)).store_with_cache ((Model.spec (V := V)).on_block_with .alsoCarried E hc cfg st B) ((Model.spec (V := V)).contractCache contract), some B) := by
  intro contract E hc cfg nd st B D hD h hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  obtain ⟨B', h2, h1⟩ := DutiesReached.propose_out hinv hconf hD
  rw [h2] at h
  cases h
  have hd : NoRaise.DistinctRoots (Spec.Protocol.on_block
      (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E) st.val B').T := by
    have := D.1.property.2.1
    rw [h1] at this
    exact this
  obtain ⟨D1, D2⟩ := D
  simp only at h1 h2
  subst h2
  refine Prod.ext (Subtype.ext ?_) rfl
  show D1.val = { ((Model.spec (V := V)).on_block_with .alsoCarried E hc cfg st B'.toProofNamed).val with saved_grades := contract }
  rw [h1, DutiesReached.on_block_with_val st B' hd]

/-- At `Model.spec`, if the proposal read at a reached store `st` answers the block `B`, the
    store of every outcome of the proposal duty is the store that received `B`, with the contract's
    cache written in. -/
theorem _root_.SpecRecord.DutiesFacts.spec_propose_block_with_fst_of_some :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) {B : NamedBlock V}
      (o : Option (NamedBlock V)) (ho : (Model.spec (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o) (h : o = some B)
      (D : (Model.spec (V := V)).NS × Option (NamedBlock V)) (hD : (Model.spec (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D)
      (hn : (Model.spec (V := V)).reachedStore st),
      D.1 = (Model.spec (V := V)).store_with_cache ((Model.spec (V := V)).on_block_with .alsoCarried E hc cfg st B) ((Model.spec (V := V)).contractCache contract) := by
  intro contract E hc cfg nd st B o ho h D hD hn
  have h2 := SpecRecord.DutiesFacts.spec_propose_block_with_snd_of_some contract E hc cfg nd
    st o ho h D hD
  rw [SpecRecord.DutiesFacts.spec_propose_block_with_eq_of_snd contract E hc cfg nd st D hD
    h2 hn]

/-- At `Model.spec`, the store of an outcome `D` of the attestation duty at a reached store
    `st` is `st` after admitting `D`'s attestation, with the contract's cache written in. -/
theorem _root_.SpecRecord.DutiesFacts.spec_namedDuties_attest_with_fst :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) (record : (Model.spec (V := V)).NR)
      (D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V) (hD : (Model.spec (V := V)).duties_attest_with contract E hc nd st record ⇢ D)
      (hn : (Model.spec (V := V)).reachedStore st),
      D.1 = (Model.spec (V := V)).store_with_cache ((Model.spec (V := V)).admit_row hc st D.2.2) ((Model.spec (V := V)).contractCache contract) := by
  intro contract E hc nd st record D hD hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  obtain ⟨p, -, h1, h2⟩ := DutiesReached.attest_out hinv hconf hD
  apply Subtype.ext
  show D.1.val = { (Member.admit_row hc st.val D.2.2) with saved_grades := contract }
  rw [h1, h2]
  show _ = { Spec.Protocol.admit_attestation _ st.val
    (Spec.Attestation.toSpecNamed p.2.toProofNamed) with saved_grades := contract }
  rw [Spec.Attestation.toSpecNamed_toProofNamed]
  rfl

/-- At `Model.spec`, the store of an outcome of the attestation duty at a reached store `st` is
    `st` after admitting the attestation of any outcome `A` of the round action, with the contract's
    cache written in. -/
theorem _root_.SpecRecord.DutiesFacts.spec_namedDuties_attest_with_fst_eq_round_action :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) (record : (Model.spec (V := V)).NR)
      (D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V) (hD : (Model.spec (V := V)).duties_attest_with contract E hc nd st record ⇢ D)
      (A : (Model.spec (V := V)).NR × NamedAttestation V) (hA : (Model.spec (V := V)).round_action_with contract E hc nd ((Model.spec (V := V)).toHealing st.core) record ⇢ A)
      (hn : (Model.spec (V := V)).reachedStore st),
      D.1 = (Model.spec (V := V)).store_with_cache ((Model.spec (V := V)).admit_row hc st A.2) ((Model.spec (V := V)).contractCache contract) := by
  intro contract E hc nd st record D hD A hA hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  obtain ⟨p, hp, -, h2⟩ := DutiesReached.attest_out hinv hconf hD
  obtain ⟨p', hp', hA'⟩ := ContractImages.round_action_with_shape hA
  have e : p = p' := Except.ok.inj (hp.symm.trans hp')
  subst e
  have hA2 : A.2 = D.2.2 := by rw [hA', h2]
  rw [hA2]
  exact SpecRecord.DutiesFacts.spec_namedDuties_attest_with_fst contract E hc nd st record
    D hD hn

/-! ## The two case fields of `NodeFacts` -/

open DecoupledConsensusModel.Execution
open scoped DC

/-- At `Model.spec`, the proposal duty at a reached store either keeps the store, writing the
    contract's cache, and sends nothing, or sends a block `B` and returns the store that received
    `B`, writing the contract's cache. -/
theorem _root_.SpecRecord.NodeFacts.spec_named_propose_cases :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) (gc : (Model.spec (V := V)).Contract) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.spec (V := V)).NS)
      (out : (Model.spec (V := V)).NS × Option (NamedBlock V)), (Model.spec (V := V)).duties_propose_block_with gc S.E S.hc S.cfg nd st ⇢ out →
      ∀ (hn : (Model.spec (V := V)).reachedStore st),
      out = ((Model.spec (V := V)).store_with_cache st ((Model.spec (V := V)).contractCache gc), Option.none) ∨ ∃ B, out = ((Model.spec (V := V)).store_with_cache ((Model.spec (V := V)).receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.block B)) ((Model.spec (V := V)).contractCache gc), Option.some B) := by
  intro S gc nd st out h₁ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  obtain ⟨B', h2, -⟩ := DutiesReached.propose_out hinv hconf h₁
  refine Or.inr ⟨B'.toProofNamed, ?_⟩
  rw [SpecRecord.DutiesFacts.spec_propose_block_with_eq_of_snd gc S.E S.hc S.cfg nd st out
    h₁ h2 hn]
  rfl

/-- At `Model.spec`, the Goldfish vote duty at a reached store either keeps the store, writing
    the contract's cache, and sends nothing, or sends a vote `u` and returns the store that received
    `u`, writing the contract's cache. -/
theorem _root_.SpecRecord.NodeFacts.spec_named_vote_cases :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) (gc : (Model.spec (V := V)).Contract) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.spec (V := V)).NS)
      (out : (Model.spec (V := V)).NS × Option (GoldfishVote V)), (Model.spec (V := V)).duties_goldfish_vote_with gc S.E S.hc nd st ⇢ out →
      ∀ (hn : (Model.spec (V := V)).reachedStore st),
      out = ((Model.spec (V := V)).store_with_cache st ((Model.spec (V := V)).contractCache gc), Option.none) ∨ ∃ u, out = ((Model.spec (V := V)).store_with_cache ((Model.spec (V := V)).receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u)) ((Model.spec (V := V)).contractCache gc), Option.some u) := by
  intro S gc nd st out h₁ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  rcases DutiesReached.vote_out hinv hconf h₁ with ⟨u, h2, h1⟩ | ⟨h2, h1⟩
  · refine Or.inr ⟨u.toProof, Prod.ext (Subtype.ext ?_) h2⟩
    have e : ((Model.spec (V := V)).receipt_process S st (.gfVote u.toProof)).val =
        Member.receipt_process S st.val (.gfVote u.toProof) := by
      show (OkMember.receipt_process S st (.gfVote u.toProof)).val = _
      unfold OkMember.receipt_process
      rw [dif_neg (show ¬ objectRootHeldByOther st.val.T (.gfVote u.toProof) from fun h => h.elim)]
    show out.1.val = { ((Model.spec (V := V)).receipt_process S st (.gfVote u.toProof)).val with
      saved_grades := gc }
    rw [e, h1]
    show _ = { Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec S.E)
      st.val (Spec.GoldfishVote.toSpec u.toProof) with saved_grades := gc }
    rw [Spec.GoldfishVote.toSpec_toProof]
  · exact Or.inl (Prod.ext (Subtype.ext h1) h2)

end DecoupledConsensusModel.Sts.Record

namespace SpecRecord.DutiesReached

/-! ## The core block call and the checked handler -/

open Spec
open SpecRecord.NoRaise
open SpecRecord.SubtypeEqualities
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Writing the block `W` with chain state `v` into `st`, admitting the Goldfish votes `W` includes
    and updating finality commutes with the image under `toProof`, under the stated conditions on
    `st`, `W` and `v`. -/
theorem image_write (E : DecoupledConsensusModel.Env V) {st : Store V} (hok : StoreOk st)
    (hJ : st.J ∈ st.T) (hoff : OffTreeInitial st) {W : Block V}
    (hroot : ¬ RootHeldByOther st.T W) (hp : W.parent ∈ st.T) (v : Protocol.ChainState V)
    (hvJ : v.J ∈ st.T) (hvF : v.F ∈ st.T) :
    (Handlers.updateFinalityWith
      (W.gf_votes.foldl (Protocol.on_goldfish_vote_checked (Provisional.toSpec E))
        { st with
          σ := Function.update st.σ W v
          T := st.T ∪ {W}
          timestamp_block := Function.update st.timestamp_block W (some (st.t : Stamp)) })
      ((W.gf_votes.foldl (Protocol.on_goldfish_vote_checked (Provisional.toSpec E))
        { st with
          σ := Function.update st.σ W v
          T := st.T ∪ {W}
          timestamp_block := Function.update st.timestamp_block W (some (st.t : Stamp)) }).σ W)).toProof =
    DecoupledConsensusModel.Protocol.update_finality
      ((W.toProof.gf_votes).foldl (DecoupledConsensusModel.Protocol.on_goldfish_vote_checked E)
        ({ st.toProof with
          σ := fun C => if C = W.toProof then v.toProof else st.toProof.σ C
          T := insert W.toProof st.toProof.T
          timestamp_block := fun C =>
            if C = W.toProof then some (st.toProof.t : Stamp) else st.toProof.timestamp_block C } :
          DecoupledConsensusModel.Protocol.Store V)) v.toProof := by
  obtain ⟨-, hd, hpc, hF⟩ := hok
  rw [toProof_gf_votes, toProof_write_block hd hoff hroot v, toProof_foldl_checked]
  obtain ⟨x, y, hst₂⟩ := foldl_checked_shape (Provisional.toSpec E) W.gf_votes
    { st with
          σ := Function.update st.σ W v
          T := st.T ∪ {W}
          timestamp_block := Function.update st.timestamp_block W (some (st.t : Stamp)) }
  rw [hst₂]
  have hσW : ({ { st with
          σ := Function.update st.σ W v
          T := st.T ∪ {W}
          timestamp_block := Function.update st.timestamp_block W (some (st.t : Stamp)) } with
      gf_votes := x, timestamp_vote := y } : Store V).σ W = v := Function.update_self ..
  rw [hσW]
  have hpc' : ParentClosed (st.T ∪ {W}) := by
    intro Y hY
    rcases Finset.mem_union.mp hY with hY | hY
    · exact Finset.mem_union_left _ (hpc Y hY)
    · rw [Finset.mem_singleton.mp hY]
      exact Finset.mem_union_left _ hp
  exact (toProof_updateFinalityWith
    (st := ({ { st with
          σ := Function.update st.σ W v
          T := st.T ∪ {W}
          timestamp_block := Function.update st.timestamp_block W (some (st.t : Stamp)) } with
      gf_votes := x, timestamp_vote := y } : Store V)) v (injOn_insert hd hroot) hpc'
    (Finset.mem_union_left _ hF) (Finset.mem_union_left _ hJ) (Finset.mem_union_left _ hvJ)
    (Finset.mem_union_left _ hvF)).symm

/-- `Handlers.onBlockUsing` at a block its tests accept writes the block, admits its Goldfish votes
    and updates finality. -/
theorem onBlockUsing_eq_of_pass (P : Provisional V) (st : Store V) (Y : Block V)
    (build : Protocol.ChainState V → Protocol.ChainState V)
    (h1 : ¬ st.s < Y.slot) (h2 : Y ∉ st.T) (h3 : Y.parent ∈ st.T) (h4 : st.F.ancestorEq Y = true)
    (h5 : Y.proposer? = P.proposer Y.slot) (h6 : Y.parent.slot < Y.slot) :
    Handlers.onBlockUsing P st Y build =
      Handlers.updateFinalityWith
        (Y.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with
            σ := Function.update st.σ Y (build (st.σ Y.parent))
            T := st.T ∪ {Y}
            timestamp_block := Function.update st.timestamp_block Y (some (st.t : Stamp)) })
        ((Y.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with
            σ := Function.update st.σ Y (build (st.σ Y.parent))
            T := st.T ∪ {Y}
            timestamp_block := Function.update st.timestamp_block Y (some (st.t : Stamp)) }).σ Y) := by
  unfold Handlers.onBlockUsing
  simp only [Id.run, h1, h2, h3, h4, h5, h6, List.forIn_pure_yield_eq_foldl]
  simp
  rfl

/-- At a store with the run invariant, admitting a named block `B` whose named parent is a named
    block of the store, by the core block call or by the checked handler, gives stores with one
    image. -/
theorem core_image_eq [Inhabited V] (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : OkStore V)
    (hinv : RunStoreInv st.val) (B : DecoupledConsensusModel.NamedBlock V)
    (hp : B.parent ∈ Member.bodies st.val) :
    (OkMember.ns_process_block_core E hc cfg st B).val.toProof =
      (OkMember.on_block_checked_using
        (fun current => OkMember.on_block_using E current B.erase
          (fun ps => Member.named_transition E cfg ps B)) hc st B.erase).val.toProof := by
  have hok := st.property
  obtain ⟨-, hd, hpc, hF⟩ := st.property
  obtain ⟨hJ, hcs, hoff⟩ := hinv
  have hinj := injOn_of_distinctRoots hd
  set X := Block.toSpecNamed B with hXdef
  set Y := st.val.blockOfImage B.erase with hYdef
  have hXB : X.toProofNamed = B := Block.toProofNamed_toSpecNamed B
  have hXe : X.toProof = B.erase := by rw [← Block.toProofNamed_erase, hXB]
  have hYe : Y.toProof = B.erase := Store.toProof_blockOfImage _ _
  obtain ⟨Z, hZ, hZB⟩ := Finset.mem_map.mp hp
  have hZB' : Z.toProofNamed = B.parent := hZB
  have hXpar : X.parent = Z := by
    apply Block.toProofNamed_injective
    rw [← toProofNamed_parent, hXB, hZB']
  have hYpar : Y.parent = Z := by
    rw [← Store.blockOfImage_parent st.val hinj hpc B.erase]
    have e : B.erase.parent = Z.toProof := by rw [← hXe, toProof_parent, hXpar]
    rw [e, Store.blockOfImage_toProof_of_mem st.val hd hZ]
  have hroot : Y.root = X.root := by
    have e := congrArg DecoupledConsensusModel.Block.root (hYe.trans hXe.symm)
    simpa only [Block.toProof_root, BlockId.toProof_inj] using e
  have hslot : Y.slot = X.slot := by rw [← toProof_slot, ← toProof_slot, hYe, hXe]
  have hprop : Y.proposer? = X.proposer? := by
    rw [← toProof_proposer?, ← toProof_proposer?, hYe, hXe]
  by_cases hR : ∃ W ∈ st.val.T, W.root = X.root
  · obtain ⟨W, hW, hWr⟩ := hR
    have hL : (OkMember.ns_process_block_core E hc cfg st B).val = st.val := by
      unfold OkMember.ns_process_block_core
      split
      · rfl
      · rename_i hnr
        have hX : X ∈ st.val.T := by
          by_contra hX
          exact hnr ⟨W, hW, fun e => hX (by subst e; exact hW), hWr⟩
        show Handlers.admitBlockCore _ _ st.val X = st.val
        unfold Handlers.admitBlockCore
        rw [NodeFacts.block_admissible_of_mem _ _ hX]
        rfl
    have hR' : (OkMember.on_block_checked_using
        (fun current => OkMember.on_block_using E current B.erase
          (fun ps => Member.named_transition E cfg ps B)) hc st B.erase).val = st.val := by
      unfold OkMember.on_block_checked_using
      split
      · unfold OkMember.on_block_using
        dsimp only
        split
        · rfl
        · rename_i _ hnr
          have hY : Y ∈ st.val.T := by
            by_contra hY
            exact hnr ⟨W, hW, fun e => hY (by subst e; exact hW), hWr.trans hroot.symm⟩
          show Handlers.onBlockUsing (Provisional.toSpec E) st.val Y
            (fun ps => Member.named_transition E cfg ps B) = st.val
          exact HandlersFacts.onBlockUsing_of_reject _ _ _ _ (Or.inl (Or.inr (Or.inl hY)))
      · rfl
    rw [hL, hR']
  · have hXT : X ∉ st.val.T := fun h => hR ⟨X, h, rfl⟩
    have hYT : Y ∉ st.val.T := fun h => hR ⟨Y, h, hroot⟩
    have hnrX : ¬ RootHeldByOther st.val.T X := fun ⟨W, hW, _, hWr⟩ => hR ⟨W, hW, hWr⟩
    have hnrY : ¬ RootHeldByOther st.val.T Y := fun ⟨W, hW, _, hWr⟩ =>
      hR ⟨W, hW, hWr.trans hroot⟩
    have hL : (OkMember.ns_process_block_core E hc cfg st B).val =
        Handlers.admitBlockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st.val X := by
      unfold OkMember.ns_process_block_core
      rw [dif_neg hnrX]
      rfl
    have hRv : (OkMember.on_block_checked_using
        (fun current => OkMember.on_block_using E current B.erase
          (fun ps => Member.named_transition E cfg ps B)) hc st B.erase).val =
        if Protocol.included_attestations_admissible
            (Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig)
            (Block.toSpec B.erase) then
          Handlers.onBlockUsing (Provisional.toSpec E) st.val Y
            (fun ps => Member.named_transition E cfg ps B)
        else st.val := by
      unfold OkMember.on_block_checked_using
      split_ifs
      · unfold OkMember.on_block_using
        dsimp only
        rw [dif_neg hnrY]
        rfl
      · rfl
    have hinc : Protocol.included_attestations_admissible
        (Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig)
        (Block.toSpec B.erase) =
        Protocol.included_attestations_admissible (Config.toSpec E hc cfg) X := by
      rw [← toProof_carried_attestations_admissible ChainStateToHandlers.unreadEnv hc
        unreadHeightConfig, ← toProof_carried_attestations_admissible E hc cfg,
        Block.toProof_toSpec, hXe]
    have hpcX : ParentClosed (st.val.T ∪ {X}) := by
      intro W hW
      rcases Finset.mem_union.mp hW with hW | hW
      · exact Finset.mem_union_left _ (hpc W hW)
      · rw [Finset.mem_singleton.mp hW, hXpar]
        exact Finset.mem_union_left _ hZ
    have hanc : st.val.F.ancestorEq X = st.val.F.ancestorEq Y := by
      rw [← Block.toProof_preceq_of_injOn (st.val.T ∪ {X}) (injOn_insert hd hnrX) hpcX
        (Finset.mem_union_left _ hF) (Finset.mem_union_right _ (Finset.mem_singleton_self X)), hXe]
      have e := Store.blockOfImage_ancestorEq_of_distinctRoots st.val hd hpc st.val.F.toProof
        B.erase
      rw [Store.blockOfImage_toProof_of_mem st.val hd hF] at e
      exact e.symm
    rw [hL, hRv, hinc]
    unfold Handlers.admitBlockCore
    by_cases hadm : Protocol.block_admissible (Config.toSpec E hc cfg) (Provisional.toSpec E)
        st.val X = true
    · obtain ⟨-, hia, hs, hFX, hprop', hps⟩ := (block_admissible_iff _ _ st.val X).mp hadm
      rw [if_pos hia, if_pos hadm]
      have hcsZ := hcs Z hZ
      have hvX := state_transition_blocks (Config.toSpec E hc cfg) (Provisional.toSpec E)
        (st.val.σ X.parent) X
      have hvY := state_transition_blocks (Config.toSpec E unreadHealConfig cfg)
        (Provisional.toSpec E) (st.val.σ Y.parent) (Block.toSpecNamed B)
      rw [hXpar] at hvX
      rw [hYpar] at hvY
      have hvXJ : (Protocol.state_transition (Config.toSpec E hc cfg) (Provisional.toSpec E)
          (st.val.σ X.parent) X).J ∈ st.val.T := by
        rw [hXpar]
        rcases hvX.2.2.1 with h | h <;> rw [h]
        · exact hcsZ.2.2.1
        · exact hcsZ.2.1
      have hvXF : (Protocol.state_transition (Config.toSpec E hc cfg) (Provisional.toSpec E)
          (st.val.σ X.parent) X).F ∈ st.val.T := by
        rw [hXpar]
        rcases hvX.2.2.2 with h | h <;> rw [h]
        · exact hcsZ.2.2.2
        · exact hcsZ.2.2.1
      have hvYJ : (Member.named_transition E cfg (st.val.σ Y.parent) B).J ∈ st.val.T := by
        show (Protocol.state_transition (Config.toSpec E unreadHealConfig cfg)
          (Provisional.toSpec E) (st.val.σ Y.parent) (Block.toSpecNamed B)).J ∈ st.val.T
        rw [hYpar]
        rcases hvY.2.2.1 with h | h <;> rw [h]
        · exact hcsZ.2.2.1
        · exact hcsZ.2.1
      have hvYF : (Member.named_transition E cfg (st.val.σ Y.parent) B).F ∈ st.val.T := by
        show (Protocol.state_transition (Config.toSpec E unreadHealConfig cfg)
          (Provisional.toSpec E) (st.val.σ Y.parent) (Block.toSpecNamed B)).F ∈ st.val.T
        rw [hYpar]
        rcases hvY.2.2.2 with h | h <;> rw [h]
        · exact hcsZ.2.2.2
        · exact hcsZ.2.2.1
      have hv : (Protocol.state_transition (Config.toSpec E hc cfg) (Provisional.toSpec E)
          (st.val.σ X.parent) X).toProof =
          (Member.named_transition E cfg (st.val.σ Y.parent) B).toProof := by
        show _ = (Protocol.state_transition (Config.toSpec E unreadHealConfig cfg)
          (Provisional.toSpec E) (st.val.σ Y.parent) X).toProof
        rw [hXpar, hYpar, ← toProof_named_transition E hc cfg,
          ← toProof_named_transition E unreadHealConfig cfg]
      rw [blockCore_eq, onBlockUsing_eq_of_pass _ _ _ _ (by rw [hslot]; exact hs) hYT
        (by rw [hYpar]; exact hZ) (by rw [← hanc]; exact hFX)
        (by rw [hprop, hslot]; exact hprop') (by rw [hYpar, hslot, ← hXpar]; exact hps)]
      rw [image_write E hok hJ hoff hnrX (by rw [hXpar]; exact hZ) _ hvXJ hvXF,
        image_write E hok hJ hoff hnrY (by rw [hYpar]; exact hZ) _ hvYJ hvYF, hXe, hYe, hv]
    · rw [if_neg hadm]
      split_ifs with hia
      · rw [HandlersFacts.onBlockUsing_of_reject]
        by_contra hcon
        apply hadm
        rw [block_admissible_iff]
        simp only [not_or, not_lt, not_not, Bool.not_eq_false, ne_eq] at hcon
        obtain ⟨⟨h1, -, -⟩, h4, h5, h6⟩ := hcon
        refine ⟨⟨hXT, hXpar ▸ hZ⟩, hia, ?_, ?_, ?_, ?_⟩
        · rw [← hslot]; exact not_lt.mpr h1
        · rw [hanc]; exact h4
        · rw [← hprop, ← hslot]; exact h5
        · rw [hXpar, ← hYpar, ← hslot]; exact not_le.mp h6
      · rfl

end SpecRecord.DutiesReached

namespace DecoupledConsensusModel.Sts.Record

open SpecRecord

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.BlockProcessingDefaults
open Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)
open Protocol (Record)
open Protocol (HealConfig)
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedAdmission
open Protocol.NamedAdmission
open DecoupledConsensusModel.Proofs.NamedFinalityMonotone
open Execution Protocol
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open BlockProcessingDefaults
open Internal Execution
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Internal.NamedRecoveryRead
open Protocol (ChainState)
open Protocol (Record HeightId)
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open scoped DC

/-- At `Model.spec`, if the named parent of `B` is among the named blocks of a reached store
    `st`, the core block call's store and the checked handler's store have one image. -/
theorem _root_.SpecRecord.HandlersFacts.spec_process_block_core_of_parent_mem :
    ∀ (E : Env V) (hc : Protocol.HealConfig)
      (cfg : Protocol.HeightConfig) {st : (Model.spec (V := V)).NS} {B : NamedBlock V}, B.parent ∈ st.bodies →
      ∀ (hn : (Model.spec (V := V)).reachedStore st),
      (Model.spec (V := V)).sameCore ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core
        ((Model.spec (V := V)).commitBlock st
          ((Model.spec (V := V)).on_block_checked_using
            (fun current => (Model.spec (V := V)).on_block_using E current B.erase
              (fun ps => (Model.spec (V := V)).named_transition E cfg ps B)) hc st.core B.erase) B).core := by
  intro E hc cfg st B h₁ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  exact DutiesReached.core_image_eq E hc cfg st hinv B h₁

end DecoupledConsensusModel.Sts.Record

namespace DecoupledConsensusModel.Sts.Record

open SpecRecord

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (Record)
open Internal
open Execution
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedActions
open Protocol.NamedActions
open DecoupledConsensusModel.Proofs.NamedDuties
open Protocol.NamedDuties
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (HealConfig)
open Internal.NamedRecoveryRead
open Protocol
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)

/-- At `Model.spec`, if the proposal duty at a reached store `st` proposes `B`, then `B`'s
    parent is a named block of `st`, `B` has the parent, slot, root, votes, support votes and
    proposer of every outcome `input` of the proposal input, and its attestations are those
    `proposalRows` keeps on `B`'s parent of every outcome `L` of the selection. -/
theorem _root_.SpecRecord.DutiesFacts.spec_proposal_payload :
    ∀ (contract : (Model.spec (V := V)).Contract) (source : Protocol.ProposalRowSource) (E : Env V)
      (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) (B : NamedBlock V)
      (o : Option (NamedBlock V)), (Model.spec (V := V)).proposal_with contract source E hc nd st ⇢ o → o = some B →
      ∀ input : Protocol.ProposalInput V, (Model.spec (V := V)).with_proposal_input contract E hc nd ((Model.spec (V := V)).toHealing st.core) id ⇢ input →
      ∀ L : List (NamedAttestation V), (Model.spec (V := V)).select source hc st ⇢ L →
      ∀ (hn : (Model.spec (V := V)).reachedStore st),
      B.parent ∈ st.bodies ∧ B.parent.erase = input.parent ∧
      B.slot = input.slot ∧ B.root = input.root ∧
      B.gf_votes = input.gf_votes ∧ B.gf_support_votes = input.gf_support_votes ∧
      B.attestations = (Model.spec (V := V)).proposalRows B.parent L ∧
      B.proposer? = some input.proposer := by
  intro contract source E hc nd st B o h₁ h₂ input h₃ L h₄ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  subst h₂
  have ho' : Returns (Member.proposal_with contract source E hc nd st.val) (some B) := h₁
  unfold Member.proposal_with at ho'
  obtain ⟨Bd, hBd, e⟩ := ContractImages.except_map_eq_ok ((returns_successOutcomes _ _).1 ho')
  cases Option.some.inj e
  obtain ⟨i, rows, hi, hrows, rfl⟩ := ContractImages.build_proposal_shape hBd
  obtain ⟨i', hi', rfl⟩ := ContractImages.except_map_eq_ok ((returns_successOutcomes _ _).1 h₃)
  have e' : i = i' := Except.ok.inj (hi.symm.trans hi')
  subst e'
  obtain ⟨L', hL', rfl⟩ := ContractImages.except_map_eq_ok ((returns_successOutcomes _ _).1 h₄)
  rw [DutiesReached.ofImage_eq_of_inv hinv hconf] at hrows
  have hrowsL : rows = L' := Except.ok.inj (hrows.symm.trans hL')
  subst hrowsL
  obtain ⟨H, sv, -, hH, rfl⟩ := ContractImages.proposal_input_shape hi
  have hHT : H ∈ st.val.T := ContractImages.get_head_with_contractStore_mem st contract _
    (Finset.mem_image_of_mem _ hinv.1) hH
  simp only [Spec.Block.toProofNamed, Spec.Protocol.ProposalInput.toProof, id_eq,
    DecoupledConsensusModel.NamedBlock.parent, DecoupledConsensusModel.NamedBlock.slot,
    DecoupledConsensusModel.NamedBlock.root, DecoupledConsensusModel.NamedBlock.gf_votes,
    DecoupledConsensusModel.NamedBlock.gf_support_votes, DecoupledConsensusModel.NamedBlock.attestations,
    DecoupledConsensusModel.NamedBlock.proposer?]
  refine ⟨?_, ?_, trivial, trivial, trivial, trivial, ?_, trivial⟩
  · exact Finset.mem_map_of_mem Spec.Block.toProofNamedEmb hHT
  · exact Spec.Block.toProofNamed_erase _
  · show _ = (Spec.Protocol.proposal_attestations
      (Spec.Block.toSpecNamed H.toProofNamed)
      ((rows.map Spec.Attestation.toProofNamed).map
        Spec.Attestation.toSpecNamed)).map Spec.Attestation.toProofNamed
    rw [Spec.Block.toSpecNamed_toProofNamed, List.map_map]
    simp only [Function.comp_def, Spec.Attestation.toSpecNamed_toProofNamed, List.map_id']

end DecoupledConsensusModel.Sts.Record

/-!
## The fields `update_confirmation_with_toHealing_gradeView` and `propose_block_with_nonempty`
-/

namespace SpecRecord.DutiesReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Inhabited V] in
/-- The tick, step by step, with the run of each duty it takes. -/
theorem tick_detail {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 st3 st4 st5 : Spec.Store V) (sh5 : Spec.SigningHistory)
      (l1 l2 : List (Spec.NamedObject V)),
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      (condP C P n t → (Spec.Protocol.propose_block C P X n.v
          { st0 with t := t, s := C.slotOf t }).run [] = .ok (st2, l1)) ∧
      (¬ condP C P n t → st2 = { st0 with t := t, s := C.slotOf t } ∧ l1 = []) ∧
      (condV C n t → (Spec.Protocol.goldfish_vote C P n.v st2).run l1 = .ok (st3, l2)) ∧
      (¬ condV C n t → st3 = st2 ∧ l2 = l1) ∧
      (condC C n t → Spec.Protocol.update_confirmation C st3 (C.slotOf t - 1) = .ok st4) ∧
      (¬ condC C n t → st4 = st3) ∧
      (condA C n t → (Spec.Protocol.attest C n.v st4 n.signingHistory).run l2 =
          .ok ((st5, sh5), sent)) ∧
      (¬ condA C n t → st5 = st4 ∧ sh5 = n.signingHistory ∧ sent = l2) ∧
      n' = { v := n.v, st := Spec.make_grades_compatible_with_finalized st5,
             signingHistory := sh5, awakeSince := (Spec.record_awake n t).awakeSince } := by
  unfold condP condV condC condA
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
  rw [record_awake_st] at h0
  simp only [record_awake_v, record_awake_sh] at h1 h2 h3 h4 ⊢
  have h3' : l3 = l2 := by
    split_ifs at h3
    · rw [liftM_run] at h3; exact h3.2
    · rw [pure_run] at h3; simp only [Prod.mk.injEq] at h3; exact h3.2
  subst h3'
  refine ⟨st0, st2, st3, st4, st5, sh5, l1, l3, h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro hc
    rw [if_pos hc] at h1
    exact h1
  · intro hc
    rw [if_neg hc, pure_run] at h1
    simp only [Prod.mk.injEq] at h1
    exact ⟨h1.1, h1.2⟩
  · intro hc
    rw [if_pos hc] at h2
    exact h2
  · intro hc
    rw [if_neg hc, pure_run] at h2
    simp only [Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩
  · intro hc
    rw [if_pos hc, liftM_run] at h3
    exact h3.1
  · intro hc
    rw [if_neg hc, pure_run] at h3
    simp only [Prod.mk.injEq] at h3
    exact h3.1
  · intro hc
    rw [if_pos hc] at h4
    exact h4
  · intro hc
    rw [if_neg hc, pure_run] at h4
    simp only [Prod.mk.injEq] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
    exact ⟨rfl, rfl, rfl⟩

end SpecRecord.DutiesReached

namespace SpecRecord.DutiesReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise SpecRecord.GradesRunFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The store a member duty hands the spec, at a reached store -/

/-- `Inv3 st`: `st` is of the store type, satisfies the run invariant, and holds its confirmation
    records in its tree. -/
def Inv3 (st : Spec.Store V) : Prop :=
  StoreOk st ∧ SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st

omit [Fintype V] [Inhabited V] in
/-- Saved grades already at round `r` are brought to `r` unchanged. -/
theorem advance_to_round_self (c : Spec.SavedGrades V) {r : Spec.Round}
    (h : c.round = r) : Spec.Protocol.advance_to_round c r = c := by
  unfold Spec.Protocol.advance_to_round
  rw [if_pos h.symm]

/-- On a store `X` with `Inv3` and saved grades `c` of tree blocks at round `r`, reading `X` and `c`
    through the tree and bringing `c` to `r` gives `X` with the saved grades `c`. -/
theorem handed_eq (X : Spec.Store V) (hX : Inv3 X) {c : Spec.SavedGrades V}
    (hc : Spec.Store.ContractInTree X.T c) {r : Spec.Round} (hr : c.round = r) :
    ({ Spec.Store.ofImage X with
        saved_grades := Spec.Protocol.advance_to_round (X.contractOfImage c) r } :
      Spec.Store V) = { X with saved_grades := c } := by
  obtain ⟨hok, hR, hC⟩ := hX
  rw [Spec.Store.ofImage_eq_self X hok.2.1 hok.2.2.2 hR.1 hC.1 hC.2.1 hC.2.2,
    Spec.Store.contractOfImage_of_distinctRoots X hok.2.1 hc, advance_to_round_self c hr]

omit [Fintype V] [Inhabited V] in
/-- If the saved grades hold blocks of `T` only, every result they hold is a block of `T` or none. -/
theorem claim_of_contractInTree {T : Finset (Spec.Block V)}
    {c : Spec.SavedGrades V} (h : Spec.Store.ContractInTree T c) :
    CacheClaim c (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
  have key : ∀ (r : Round) (f : Spec.RoundGrades V), f ∈ [c.current, c.next] →
      FrameClaim r f (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
    intro r f hf p G hG g hg
    subst hg
    have hmem : res f p ∈ [f.g0, f.g1, f.g2] := by
      cases p <;> simp [res, Spec.Protocol.phaseResult,
        Spec.Protocol.Phase.toSpec]
    exact h f hf (res f p) hmem g hG
  exact ⟨key _ _ (by simp), key _ _ (by simp)⟩

/-- For an outcome `c` of `onPhaseTick` at `t` on a reached node state, the spec's grades update of
    the tick at `t` on the node's store answers a store whose saved grades are `c`, at the round of
    `t`'s slot and holding blocks of the node's tree only. -/
theorem onPhaseTick_eq (S : Setup V) (n : (Model.spec (V := V)).N) (t : Time)
    (hn : (Model.spec (V := V)).reachedNode n) {c : (Model.spec (V := V)).Cache}
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c) :
    ∃ st0 : Spec.Store V,
      Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P n.val.st t =
        .ok st0 ∧ c = st0.saved_grades ∧
      st0 = { n.val.st with saved_grades := c } ∧
      c.round = (Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t) ∧
      Spec.Store.ContractInTree n.val.st.T c := by
  obtain ⟨st0, h0, rfl, -⟩ := SpecRecord.GradesFacts.sd_onPhaseTick_ok hc
  have h0' : Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P
      n.val.st t = .ok st0 := h0
  obtain ⟨e0, hr⟩ := update_grades_ok h0'
  refine ⟨st0, h0', rfl, e0, hr, ?_⟩
  exact contractInTree_of_claim (memClaim_update_grades n.property h0'
    (claim_of_contractInTree (reached_elim hn).2.2))

omit [Inhabited V] in
/-- Two sets of external values with the same roots of new blocks for `v` give `v` the same proposal
    duty. -/
theorem propose_block_external {C : Spec.Config} {P : Spec.Provisional V}
    {X₁ X₂ : Spec.External V} {v : V} (h : X₁.new_root v = X₂.new_root v)
    (st : Spec.Store V) :
    Spec.Protocol.propose_block C P X₁ v st =
      Spec.Protocol.propose_block C P X₂ v st := by
  unfold Spec.Protocol.propose_block Spec.Protocol.build_proposal
    Spec.Protocol.proposal_input
  rw [h]


end SpecRecord.DutiesReached

namespace SpecRecord.DutiesReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Inhabited V] in
/-- The spec's tick keeps the tree of its store after the proposal duty. -/
theorem tick_T_after_proposal {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 : Spec.Store V) (l1 : List (Spec.NamedObject V)),
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      (condP C P n t → (Spec.Protocol.propose_block C P X n.v
          { st0 with t := t, s := C.slotOf t }).run [] = .ok (st2, l1)) ∧
      st2.T ⊆ n'.st.T := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, -, hV1, hV0, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_detail h
  refine ⟨st0, st2, l1, h0, hP1, ?_⟩
  have h3 : st3.T = st2.T := by
    by_cases hc : condV C n t
    · obtain ⟨x, y, e⟩ := ContractImages.goldfish_vote_writes (hV1 hc)
      have e' : st3 = { st2 with gf_votes := x, timestamp_vote := y } := e
      rw [e']
    · rw [(hV0 hc).1]
  have h4 : st4.T = st3.T := by
    by_cases hc : condC C n t
    · rw [NoRaise.update_confirmation_writes_only_confirmation (hC1 hc)]
    · rw [hC0 hc]
  have h5 : st4.T ⊆ st5.T := by
    by_cases hc : condA C n t
    · obtain ⟨row, -, hst5, -⟩ := NodeFacts.attest_run (hA1 hc)
      rw [hst5]
      exact (NodeFacts.keeps_admit_attestation _ _ _).2.2.1
    · rw [(hA0 hc).1]
  rw [hn']
  show st2.T ⊆ (Spec.make_grades_compatible_with_finalized st5).T
  have e : (Spec.make_grades_compatible_with_finalized st5).T = st5.T := rfl
  rw [e, ← h3, ← h4]
  exact h5

/-- At `Model.spec`, at a proposal time of a reached node state running as its proposer, the
    proposal duty has an outcome. -/
theorem _root_.SpecRecord.DutiesFacts.spec_propose_block_with_nonempty :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (hs : 0 < S.E.slotOf t) (ht : t = (Model.spec (V := V)).proposal_time S.E (S.E.slotOf t))
      (hv : S.E.proposer (S.E.slotOf t) = v)
      (hawake : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc (S.E.slotOf t)))
      (c : (Model.spec (V := V)).Cache) (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
      (hn : (Model.spec (V := V)).reachedNode n) (hruns : (Model.spec (V := V)).runs_as n v),
      ∃ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
        (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).frameContract c) S.E S.hc S.cfg (S.node v)
          ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D := by
  intro S v n t out hout hs ht hv hawake c hc hn hruns
  have hruns' : n.val.v = v := hruns
  obtain ⟨sent, hrun, -⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, l1, h0, hP1, hsub⟩ := tick_T_after_proposal hrun
  have hsl := NodeFacts.slotOf_eq S t
  have hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
    refine ⟨by rw [hsl]; exact hs, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hsl]; exact ht
    · rw [hsl, hruns']; exact hv
    · obtain ⟨a, ha, hle⟩ := hawake
      exact (record_awake_awake_since n.val t _).mpr (Or.inl ⟨a, ha, by rw [hsl]; exact hle⟩)
  have hprop := hP1 hcP
  obtain ⟨st0', h0', hc0, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc
  have est : st0' = st0 := Except.ok.inj (h0'.symm.trans h0)
  rw [est] at e0 hc0
  obtain ⟨h1, h2, -⟩ := reached_elim hn
  set X := (Model.spec (V := V)).ns_setClock S.E n.st t with hXdef
  have hstage : ({ X.val with saved_grades := c } : Spec.Store V) =
      { st0 with t := t, s := (Setup.toSpec S).C.slotOf t } := by rw [e0]; rfl
  have hX : Inv3 X.val := ⟨X.property, h1, h2⟩
  have hext : (Member.externalOfNode (S.node v)).new_root (S.node v).val_index =
      (Setup.toSpec S).X.new_root (S.node v).val_index := by
    rw [S.node_val_index]; rfl
  have h' : (Spec.Protocol.propose_block (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) (Member.externalOfNode (S.node v)) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s)) }).run [] =
        .ok (st2, l1) := by
    rw [handed_eq X.val hX hct (r := (Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s) hr,
      propose_block_external hext, S.node_val_index, hstage, ← hruns']
    exact hprop
  have hr1 := Member.duties_propose_block_with_returns_of_ok c S.E S.hc S.cfg (S.node v) X.val h'
  -- the store the duty answers is of the store type
  obtain ⟨B, hst2, -⟩ := NodeFacts.propose_block_run hprop
  have hokK : StoreOk ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V) := by
    rw [← hstage]; exact NonEmpty.storeOk_with_saved_grades X.property c
  have hd2 : DistinctRoots st2.T := by
    have hfin : StoreOk out.1.val.st := out.1.property
    intro Y hY Z hZ e
    exact hfin.2.1 Y (hsub hY) Z (hsub hZ) e
  have hok2 : StoreOk st2 := by
    by_cases hroot : RootHeldByOther
        ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V).T B
    · rw [hst2] at hd2 ⊢
      rw [on_block_of_rootHeld _ _ _ _ hroot hd2]
      exact hokK
    · rw [hst2]
      exact OkStore.on_block _ _ hokK hroot
  exact ⟨(⟨{ st2 with saved_grades := c }, NonEmpty.storeOk_with_saved_grades hok2 c⟩,
    (Member.firstSentBlock l1).map Spec.Block.toProofNamed),
    (returns_preimageOutcomes _ _ _).2 hr1⟩

/-- At `Model.spec`, at a reached store, the confirmation update keeps the grade view. -/
theorem _root_.SpecRecord.DutiesFacts.spec_update_confirmation_with_toHealing_gradeView :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot) (st' : (Model.spec (V := V)).S), (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ∀ (hn : (Model.spec (V := V)).reachedCore st), ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing st')) =
      ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing st)) := by
  intro contract E hc st s st' h₁ hn
  obtain ⟨hinv, hconf, -⟩ := reachedCore_elim hn
  obtain ⟨x1, x2, x3, he⟩ :=
    ContractImages.update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h₁)
  have hof : Spec.Store.ofImage st.val = st.val :=
    Spec.Store.ofImage_eq_self _ st.property.2.1 st.property.2.2.2 hinv.1 hconf.1 hconf.2.1
      hconf.2.2
  apply Subtype.ext
  show Member.gradeView st'.val = Member.gradeView st.val
  rw [he, hof]
  rfl

end SpecRecord.DutiesReached
