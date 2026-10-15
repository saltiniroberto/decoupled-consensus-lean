module
public import Proofs.Vocabulary.Protocol.ChainState.EntryHeight
public import Proofs.Vocabulary.Execution.NamedAncestry
public import Proofs.Vocabulary.Protocol.ChainState.NamedNjGap
public import Proofs.Vocabulary.Protocol.ChainState.ProgressQuorumCore
public import Proofs.Vocabulary.Protocol.ChainState.TargetedTimeoutBinding
public import Proofs.Vocabulary.Protocol.ChainState.W4FKChainCheckpointAlgebra
public import Proofs.Vocabulary.Protocol.Handlers.BlockProcessingDefaults
public import Proofs.Claims.Spec2Claims.Claim13bModel_fold_rows
public import Proofs.Claims.Spec2Claims.Claim13bModel_named_transition
public import Proofs.Vocabulary.Protocol.ChainState.Certificates

@[expose] public section

/-!
# Facts about `Protocol.derive_named`

The chain state of a named block: its justified and finalized blocks are named ancestors that are
their own height entries, and a block's finalized block is its parent's finalized or justified
block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.slot
  DecoupledConsensusModel.NamedBlock.Preceq DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.NamedBlock.erase DecoupledConsensusModel.NamedBlock.parent
  DecoupledConsensusModel.Protocol.ChainState.targetQuorum
  DecoupledConsensusModel.Protocol.TimeoutBinding.targeted
  DecoupledConsensusModel.Protocol.TimeoutBinding.view
  DecoupledConsensusModel.Protocol.finalityReady

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol (ChainState HeightConfig derive_named fold_rows TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

section ChainStateBodies

attribute [local semireducible] Protocol.derive_named Protocol.named_transition
  Protocol.transition_rows Protocol.ChainState.initial Protocol.process_attestation_with
  Protocol.process_attestation Protocol.process_height_events Protocol.targetReady
  Protocol.progReady Protocol.nonjustifiable Protocol.fold_rows Protocol.advance_height

/-- The justified block of `B`'s chain state is the erasure of a named ancestor `J` of `B` that is
    the entry of its own height, and that height is `B`'s justified height unless that is `0` and
    `J` is genesis; the same holds for the finalized block and the finalized height. -/
theorem derive_named_checkpoint_entries (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (∃ J : NamedBlock V, NamedBlock.Preceq J B ∧ J.erase = (derive_named E cfg B).J ∧
        (derive_named E cfg J).T_h = J.erase ∧
        (((derive_named E cfg B).h_j = 0 ∧ J = .genesis) ∨
          (derive_named E cfg J).h = (derive_named E cfg B).h_j)) ∧
      (∃ F : NamedBlock V, NamedBlock.Preceq F B ∧ F.erase = (derive_named E cfg B).F ∧
        (derive_named E cfg F).T_h = F.erase ∧
        (((derive_named E cfg B).h_F = 0 ∧ F = .genesis) ∨
          (derive_named E cfg F).h = (derive_named E cfg B).h_F)) := by
  induction B with
  | genesis =>
      exact ⟨⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩,
        ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  | node p s root gv gsv ats proposer ih =>
      obtain ⟨⟨JP, hJPle, hJPerase, hJPself, hJPheight⟩,
        ⟨FP, hFPle, hFPerase, hFPself, hFPheight⟩⟩ := ih
      have hext : ∀ {A : NamedBlock V}, NamedBlock.Preceq A p →
          NamedBlock.Preceq A (.node p s root gv gsv ats proposer) :=
        fun h => Proofs.NamedAncestry.named_extend s root gv gsv ats proposer h
      set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        (NamedBlock.node p s root gv gsv ats proposer).erase
        (NamedBlock.node p s root gv gsv ats proposer).attestations with htau
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg tau := rfl
      have hfields := Proofs.NamedDerivationGeometry.fold_context_fields
        (TimeoutBinding.targeted V)
        (NamedBlock.node p s root gv gsv ats proposer).attestations
        { derive_named E cfg p with
          s := (NamedBlock.node p s root gv gsv ats proposer).erase.slot }
      have htauH : tau.h = (derive_named E cfg p).h := hfields.2.1
      have htauT : tau.T_h = (derive_named E cfg p).T_h := hfields.2.2.1
      have htauJ : tau.J = (derive_named E cfg p).J := hfields.2.2.2.1
      have htauHj : tau.h_j = (derive_named E cfg p).h_j := hfields.2.2.2.2.1
      have htauF : tau.F = (derive_named E cfg p).F := hfields.2.2.2.2.2.1
      have htauHF : tau.h_F = (derive_named E cfg p).h_F := hfields.2.2.2.2.2.2
      obtain ⟨entry, hentryLe, hentryErase, hentryHeight⟩ :=
        Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg p
      have hentrySelf : (derive_named E cfg entry).T_h = entry.erase :=
        (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hentryLe hentryHeight).trans
          hentryErase.symm
      have hJhalf : ∃ J : NamedBlock V,
          NamedBlock.Preceq J (.node p s root gv gsv ats proposer) ∧
          J.erase = (derive_named E cfg (.node p s root gv gsv ats proposer)).J ∧
          (derive_named E cfg J).T_h = J.erase ∧
          (((derive_named E cfg (.node p s root gv gsv ats proposer)).h_j = 0 ∧
              J = .genesis) ∨
            (derive_named E cfg J).h =
              (derive_named E cfg (.node p s root gv gsv ats proposer)).h_j) := by
        by_cases htarget : Protocol.targetReady E (Protocol.afterFin E tau) = true
        · refine ⟨entry, hext hentryLe, ?_, hentrySelf, Or.inr ?_⟩
          · rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
              Protocol.advance_height_J, Protocol.afterFin_T_h, htauT, hentryErase]
          · rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
              Protocol.advance_height_h_j, Protocol.afterFin_h, htauH, hentryHeight]
        · refine ⟨JP, hext hJPle, ?_, hJPself, ?_⟩
          · rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
            split_ifs
            · rw [Protocol.advance_height_J, Protocol.afterFin_J, htauJ, hJPerase]
            · rw [Protocol.afterFin_J, htauJ, hJPerase]
          · have hsame : (derive_named E cfg
                (.node p s root gv gsv ats proposer)).h_j =
                (derive_named E cfg p).h_j := by
              rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
              split_ifs
              · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, htauHj]
              · rw [Protocol.afterFin_h_j, htauHj]
            rw [hsame]
            exact hJPheight
      refine ⟨hJhalf, ?_⟩
      by_cases hfin : Protocol.finalityReady E tau = true
      · have hFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).F =
            (derive_named E cfg p).J := by
          rw [hderive, Protocol.process_height_events_F, Protocol.afterFin_F, if_pos hfin,
            htauJ]
        have hHFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).h_F =
            (derive_named E cfg p).h_j := by
          rw [hderive, Protocol.process_height_events_h_F, Protocol.afterFin_h_F, if_pos hfin,
            htauHj]
        exact ⟨JP, hext hJPle, by rw [hJPerase, hFout], hJPself,
          by rw [hHFout]; exact hJPheight⟩
      · have hFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).F =
            (derive_named E cfg p).F := by
          rw [hderive, Protocol.process_height_events_F, Protocol.afterFin_F, if_neg hfin,
            htauF]
        have hHFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).h_F =
            (derive_named E cfg p).h_F := by
          rw [hderive, Protocol.process_height_events_h_F, Protocol.afterFin_h_F, if_neg hfin,
            htauHF]
        exact ⟨FP, hext hFPle, by rw [hFPerase, hFout], hFPself,
          by rw [hHFout]; exact hFPheight⟩

/-- For a named block `B` other than genesis, the finalized block of `B`'s chain state is the
    finalized or the justified block of its parent's chain state. -/
theorem derive_named_F_cases (E : Env V) (cfg : HeightConfig) {B : NamedBlock V}
    (hB : B ≠ .genesis) :
    (derive_named E cfg B).F = (derive_named E cfg B.parent).F ∨
      (derive_named E cfg B).F = (derive_named E cfg B.parent).J := by
  cases B with
  | genesis => exact absurd rfl hB
  | node p s root gv gsv ats proposer =>
      set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        (NamedBlock.node p s root gv gsv ats proposer).erase
        (NamedBlock.node p s root gv gsv ats proposer).attestations with htau
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg tau := rfl
      have hfields := Proofs.NamedDerivationGeometry.fold_context_fields
        (TimeoutBinding.targeted V)
        (NamedBlock.node p s root gv gsv ats proposer).attestations
        { derive_named E cfg p with
          s := (NamedBlock.node p s root gv gsv ats proposer).erase.slot }
      have htauJ : tau.J = (derive_named E cfg p).J := hfields.2.2.2.1
      have htauF : tau.F = (derive_named E cfg p).F := hfields.2.2.2.2.2.1
      have hpar : (NamedBlock.node p s root gv gsv ats proposer).parent = p := rfl
      rw [hpar]
      by_cases hfin : Protocol.finalityReady E tau = true
      · right
        rw [hderive, Protocol.process_height_events_F, Protocol.afterFin_F, if_pos hfin, htauJ]
      · left
        rw [hderive, Protocol.process_height_events_F, Protocol.afterFin_F, if_neg hfin, htauF]

/-! ## The chain state of genesis -/

/-- The chain state of genesis has height `1`. -/
theorem derive_named_genesis_h (E : Env V) (cfg : HeightConfig) :
    (derive_named E cfg (.genesis : NamedBlock V)).h = 1 := rfl

/-- The chain state of genesis has justified height `0`. -/
theorem derive_named_genesis_h_j (E : Env V) (cfg : HeightConfig) :
    (derive_named E cfg (.genesis : NamedBlock V)).h_j = 0 := rfl

/-- The finalized block of the chain state of genesis is genesis. -/
theorem derive_named_genesis_F (E : Env V) (cfg : HeightConfig) :
    (derive_named E cfg (.genesis : NamedBlock V)).F = Block.genesis := rfl

/-! ## A block whose height is its parent's plus one -/

/-- If `T_h(p).slot + timeoutDelay ≤ s`, and every member of a quorum `Q` is in `progress(p)` or
    signs a row of the block whose height pair matches `(h(p), T_h(p).root)`, then
    `h(node p s …) = h(p) + 1`. -/
theorem derive_named_node_h_eq_succ_of_progressQuorum (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId) (gv gsv : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) (Q : Finset V)
    (hQ : E.electorate.IsQuorum Q)
    (hmature : (derive_named E cfg p).T_h.slot + cfg.timeoutDelay ≤ s)
    (hcover : ∀ v ∈ Q, v ∈ (derive_named E cfg p).progress ∨
      ∃ a ∈ rows, a.val_index = v ∧
        a.height_pair.matchesEntry (derive_named E cfg p).h
          (derive_named E cfg p).T_h.root = true) :
    (derive_named E cfg (.node p s root gv gsv rows proposer)).h =
      (derive_named E cfg p).h + 1 := by
  have hsub : ∀ (rows' : List (NamedAttestation V)) (st : ChainState V),
      st.progress ⊆
        (rows'.foldl (Protocol.process_attestation_with (TimeoutBinding.targeted V)) st).progress := by
    intro rows'
    induction rows' with
    | nil => intro st; exact Finset.Subset.refl _
    | cons row rows' ih =>
        intro st
        rw [List.foldl_cons]
        apply Finset.Subset.trans _ (ih _)
        intro signer hsigner
        rw [(Proofs.TargetedTimeoutBinding.process_height_fields st row).1]
        split_ifs
        · exact Finset.mem_insert_of_mem hsigner
        · exact hsigner
  have hmem : ∀ {a : NamedAttestation V} (rows' : List (NamedAttestation V)) (st : ChainState V),
      a ∈ rows' → a.height_pair.matchesEntry st.h st.T_h.root = true →
      a.val_index ∈
        (rows'.foldl (Protocol.process_attestation_with (TimeoutBinding.targeted V)) st).progress := by
    intro a rows'
    induction rows' with
    | nil => intro st ha _; simp at ha
    | cons row rows' ih =>
        intro st ha hmatch
        rw [List.foldl_cons]
        rcases List.mem_cons.mp ha with rfl | htail
        · apply hsub
          rw [(Proofs.TargetedTimeoutBinding.process_height_fields st a).1, if_pos hmatch]
          exact Finset.mem_insert_self _ _
        · apply ih _ htail
          have hfields := Proofs.TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) st row
          rw [hfields.2.1, hfields.2.2.1]
          exact hmatch
  have hslot : ∀ (rows' : List (NamedAttestation V)) (st : ChainState V),
      (rows'.foldl (Protocol.process_attestation_with (TimeoutBinding.targeted V)) st).s =
        st.s := by
    intro rows'
    induction rows' with
    | nil => intro st; rfl
    | cons row rows' ih =>
        intro st
        rw [List.foldl_cons, ih]
        unfold Protocol.process_attestation_with
        unfold Protocol.process_attestation
        split_ifs <;> rfl
  set sigma := derive_named E cfg p with hsigma
  set st : ChainState V :=
    { sigma with s := (NamedBlock.node p s root gv gsv rows proposer).erase.slot } with hst
  have hfields := Proofs.NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows st
  have hderive : derive_named E cfg (.node p s root gv gsv rows proposer) =
      Protocol.process_height_events E cfg
        (fold_rows (TimeoutBinding.targeted V) sigma
          (NamedBlock.node p s root gv gsv rows proposer).erase rows) := rfl
  have hq : E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma
        (NamedBlock.node p s root gv gsv rows proposer).erase rows).progress := by
    apply Protocol.isQuorum_of_subset hQ
    intro v hv
    rcases hcover v hv with hprog | ⟨a, ha, hav, hmatch⟩
    · exact hsub rows st hprog
    · rw [← hav]
      exact hmem rows st ha hmatch
  have hmature' :
      (fold_rows (TimeoutBinding.targeted V) sigma
          (NamedBlock.node p s root gv gsv rows proposer).erase rows).T_h.slot +
        cfg.timeoutDelay ≤
      (fold_rows (TimeoutBinding.targeted V) sigma
          (NamedBlock.node p s root gv gsv rows proposer).erase rows).s := by
    show (rows.foldl (Protocol.process_attestation_with (TimeoutBinding.targeted V)) st).T_h.slot +
        cfg.timeoutDelay ≤
      (rows.foldl (Protocol.process_attestation_with (TimeoutBinding.targeted V)) st).s
    rw [hfields.2.2.1, hslot rows st]
    exact hmature
  rw [hderive, Proofs.NjGap.advances_of_progress_quorum E cfg hmature' hq]
  show (rows.foldl (Protocol.process_attestation_with (TimeoutBinding.targeted V)) st).h + 1 =
    sigma.h + 1
  rw [hfields.2.1]

/-! ## Chain-state facts on an arbitrary named block -/

/-- Either nothing is finalized on `D`'s chain, or the finalized block of `D`'s chain state is the
    erasure of a named ancestor `Fn` of `D` whose own chain state is at the finalization height and
    has `Fn` as that height's entry. -/
theorem finalized_is_entry (E : Env V) (cfg : Protocol.HeightConfig) (D : NamedBlock V) :
    (Protocol.derive_named E cfg D).h_F = 0 ∨
      ∃ Fn : NamedBlock V, NamedBlock.Preceq Fn D ∧
        Fn.erase = (Protocol.derive_named E cfg D).F ∧
        (Protocol.derive_named E cfg Fn).h = (Protocol.derive_named E cfg D).h_F ∧
        (Protocol.derive_named E cfg Fn).T_h = Fn.erase := by
  induction D with
  | genesis => exact Or.inl rfl
  | node parent s root votes support rows proposer ih =>
    have hstate : Protocol.derive_named E cfg (.node parent s root votes support rows proposer) =
        Protocol.process_height_events E cfg (Protocol.fold_rows
          (Protocol.TimeoutBinding.targeted V) (Protocol.derive_named E cfg parent)
          (NamedBlock.node parent s root votes support rows proposer).erase
          (NamedBlock.node parent s root votes support rows proposer).attestations) := rfl
    have hafter : (Protocol.afterFin E (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
          (Protocol.derive_named E cfg parent)
          (NamedBlock.node parent s root votes support rows proposer).erase
          (NamedBlock.node parent s root votes support rows proposer).attestations)).h_F = 0 ∨
        ∃ Fn : NamedBlock V,
          NamedBlock.Preceq Fn (.node parent s root votes support rows proposer) ∧
          Fn.erase = (Protocol.afterFin E (Protocol.fold_rows
            (Protocol.TimeoutBinding.targeted V) (Protocol.derive_named E cfg parent)
            (NamedBlock.node parent s root votes support rows proposer).erase
            (NamedBlock.node parent s root votes support rows proposer).attestations)).F ∧
          (Protocol.derive_named E cfg Fn).h = (Protocol.afterFin E (Protocol.fold_rows
            (Protocol.TimeoutBinding.targeted V) (Protocol.derive_named E cfg parent)
            (NamedBlock.node parent s root votes support rows proposer).erase
            (NamedBlock.node parent s root votes support rows proposer).attestations)).h_F ∧
          (Protocol.derive_named E cfg Fn).T_h = Fn.erase := by
      rw [Protocol.afterFin_F, Protocol.afterFin_h_F]
      split_ifs
      · obtain ⟨J, hJ, hJerase, hJself, -, hJheight⟩ :=
          Proofs.HealingSurface.namedJustificationWitness E cfg parent
        rcases hJheight with hz | hJheight
        · left
          rw [fold_rows_h_j]
          exact hz
        · right
          refine ⟨J, Proofs.NamedAncestry.named_extend s root votes support rows proposer hJ,
            ?_, ?_, hJself⟩
          · rw [fold_rows_J]
            exact hJerase
          · rw [fold_rows_h_j]
            exact hJheight
      · rcases ih with hz | ⟨Fn, hFn, herase, hheight, hself⟩
        · left
          rw [fold_rows_h_F]
          exact hz
        · right
          refine ⟨Fn, Proofs.NamedAncestry.named_extend s root votes support rows proposer hFn,
            ?_, ?_, hself⟩
          · rw [fold_rows_F]
            exact herase
          · rw [fold_rows_h_F]
            exact hheight
    rw [hstate, Protocol.process_height_events_eq]
    split_ifs <;> exact hafter

/-- If `B`'s chain-state height is at least `2`, then some named ancestor of `B` has that same
    height, and its height is its parent's plus one. -/
theorem exists_crossing_ancestor (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (hpos : 2 ≤ (Protocol.derive_named E cfg B).h) :
    ∃ N : NamedBlock V, NamedBlock.Preceq N B ∧
      (Protocol.derive_named E cfg N).h = (Protocol.derive_named E cfg B).h ∧
      (Protocol.derive_named E cfg N).h = (Protocol.derive_named E cfg N.parent).h + 1 := by
  induction B with
  | genesis =>
      exfalso
      have hone : (Protocol.derive_named E cfg (NamedBlock.genesis : NamedBlock V)).h = 1 := rfl
      rw [hone] at hpos
      exact absurd hpos (by decide)
  | node parent s root votes support rows proposer ih =>
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg parent s root votes
        support rows proposer with hstay | hstep
      · have hpar : 2 ≤ (Protocol.derive_named E cfg parent).h := by
          rw [← hstay]; exact hpos
        obtain ⟨N, hNle, hNh, hNstep⟩ := ih hpar
        exact ⟨N, Proofs.NamedAncestry.named_extend s root votes support rows proposer hNle,
          hNh.trans hstay.symm, hNstep⟩
      · exact ⟨.node parent s root votes support rows proposer,
          Proofs.NamedAncestry.named_self _, rfl, hstep⟩

section L85

open DecoupledConsensusModel.Proofs

variable (E : Env V) (cfg : Protocol.HeightConfig)

/-- A node's chain state is the transition of its parent's chain state by the node. -/
theorem derive_node_l85 (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    Protocol.derive_named E cfg (.node p s root votes support rows proposer) =
      Protocol.process_height_events E cfg
        (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) (Protocol.derive_named E cfg p)
          (NamedBlock.node p s root votes support rows proposer).erase rows) := rfl

/-- `Protocol.afterFin` keeps the slot. -/
theorem afterFin_s_l85 (σ : Protocol.ChainState V) : (Protocol.afterFin E σ).s = σ.s := by
  unfold Protocol.afterFin; split_ifs <;> rfl

/-- If `h(node p …) = h(p) + 1`, then `h_j(node p …) = h(p)`, or `p`'s chain state has `nj` set, or
    `T_h(p).slot + timeoutDelay ≤ s`. -/
theorem advance_cases_l85 (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (hup : (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h =
      (Protocol.derive_named E cfg p).h + 1) :
    (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h_j =
        (Protocol.derive_named E cfg p).h ∨
      (Protocol.derive_named E cfg p).nj = true ∨
      (Protocol.derive_named E cfg p).T_h.slot + cfg.timeoutDelay ≤ s := by
  rw [derive_node_l85] at hup ⊢
  set σf := Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
    (Protocol.derive_named E cfg p) (NamedBlock.node p s root votes support rows proposer).erase
    rows with hσf
  obtain ⟨hfh, hfT, hfnj⟩ := fold_rows_fields_l85 (Protocol.derive_named E cfg p)
    (NamedBlock.node p s root votes support rows proposer).erase rows
  have hfs : σf.s = s := by
    rw [hσf, fold_rows_s_l85]; rfl
  rw [Protocol.process_height_events_eq] at hup ⊢
  by_cases ht : Protocol.targetReady E (Protocol.afterFin E σf) = true
  · left
    rw [if_pos ht]
    rw [Protocol.advance_height_h_j]
    change (Protocol.afterFin E σf).h = _
    rw [Protocol.afterFin_h, hσf, hfh]
  · rw [if_neg ht] at hup ⊢
    by_cases hp : Protocol.progReady E cfg (Protocol.afterFin E σf) = true
    · right
      by_cases hnj : (Protocol.derive_named E cfg p).nj = true
      · exact Or.inl hnj
      · right
        have hnjf : (Protocol.afterFin E σf).nj = false := by
          rw [Protocol.afterFin_nj, hσf, hfnj]; simpa using hnj
        have htq : (Protocol.afterFin E σf).targetQuorum E = false := by
          simp only [Protocol.targetReady, hnjf, Bool.not_false, Bool.true_and] at ht
          simpa using ht
        simp only [Protocol.progReady, htq, Bool.false_or, Bool.and_eq_true,
          decide_eq_true_eq] at hp
        have hm := hp.1
        rw [Protocol.afterFin_T_h, afterFin_s_l85, hσf, hfT, fold_rows_s_l85] at hm
        exact hm
    · rw [if_neg hp, Protocol.afterFin_h, hσf, hfh] at hup
      exact absurd hup (Nat.succ_ne_self _).symm


/-- If `h(node p …) = h(p)`, then the `nj` bit of `node p …`'s chain state is the `nj` bit of `p`'s. -/
theorem derive_named_node_nj_of_h_eq (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h =
      (Protocol.derive_named E cfg p).h) :
    (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).nj =
      (Protocol.derive_named E cfg p).nj := by
  rw [derive_node_l85] at hh ⊢
  obtain ⟨hfh, -, hfnj⟩ := fold_rows_fields_l85 (Protocol.derive_named E cfg p)
    (NamedBlock.node p s root votes support rows proposer).erase rows
  rw [Protocol.process_height_events_eq] at hh ⊢
  split_ifs at hh ⊢ with h1 h2
  · rw [Protocol.advance_height_h] at hh
    change (Protocol.afterFin E _).h + 1 = _ at hh
    rw [Protocol.afterFin_h, hfh] at hh
    exact absurd hh (Nat.succ_ne_self _)
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfh] at hh
    exact absurd hh (Nat.succ_ne_self _)
  · rw [Protocol.afterFin_nj, hfnj]

/-- A chain state whose height is not a multiple of `K` has its `nj` bit clear. -/
theorem nj_false_of_not_dvd_l85 (B : NamedBlock V)
    (hK : ¬ cfg.K ∣ (Protocol.derive_named E cfg B).h) :
    (Protocol.derive_named E cfg B).nj = false := by
  obtain ⟨h_F', -, hnj⟩ := NjGap.njEntry_derive_named E cfg B
  rw [hnj]
  simp only [Protocol.nonjustifiable, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact Or.inl hK

end L85

/-- If `h(node p s …) = h(p) + 1`, then the entry `T_h` of `node p s …`'s chain state is the erasure
    of `node p s …`. -/
theorem derive_named_node_T_h_of_height_succ (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hc : (derive_named E cfg (.node p s root votes support rows proposer)).h =
      (derive_named E cfg p).h + 1) :
    (derive_named E cfg (.node p s root votes support rows proposer)).T_h =
      (NamedBlock.node p s root votes support rows proposer).erase := by
  rcases Proofs.NamedEntryHeight.transition_height_entry_cases E cfg
      (derive_named E cfg p) (.node p s root votes support rows proposer) with hs | hn
  · exact absurd (hs.1.symm.trans hc) (Nat.succ_ne_self _).symm
  · exact hn.2

/-- The chain state of a named block is the same at `E` and at `E` with its GST replaced by any
    `g ≥ 0`. -/
theorem derive_named_withGST (E : Env V) (g : Int) (hg : 0 ≤ g) (cfg : HeightConfig)
    (B : NamedBlock V) :
    derive_named { E with t_GST := g, t_GST_nonneg := hg } cfg B = derive_named E cfg B := by
  induction B with
  | genesis => rfl
  | node p s root votes support rows proposer ih =>
    rw [Proofs.BlockProcessingDefaults.derive_named_node,
      Proofs.BlockProcessingDefaults.derive_named_node, ih, named_transition_withGST]

end ChainStateBodies

end DecoupledConsensusModel.Sts
