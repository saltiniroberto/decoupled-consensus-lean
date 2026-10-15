module
public import Proofs.Vocabulary.Protocol.Handlers.Invariants2
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights

@[expose] public section

/-!
# The structure of the chain-derived state

Facts about the chain-state transition: the attestations carried along a chain, the fields
`process_attestation` and `advance_height` write, the intermediate state `afterFin` of
`process_height_events`, and the ancestry invariant `ChainOrder`.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Internal

/-! ## Ancestry and the attestations of a chain -/

section Structural

variable {V : Type} [DecidableEq V]

/-- Genesis is an ancestor of every block `B`, or `B` itself. -/
theorem preceq_genesis (B : Block V) : Block.preceq Block.genesis B = true := by
  induction B with
  | genesis => simp [Block.preceq]
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr ih

/-- A block's parent is an ancestor of the block. -/
theorem preceq_node (p : Block V) (s : Slot) (r : BlockId)
    (gv gsv : List (GoldfishVote V)) (ats : List (CombinedAttestation V)) (i : V) :
    Block.preceq p (.node p s r gv gsv ats i) = true := by
  simp only [Block.preceq, Bool.or_eq_true]
  exact Or.inr (Block.preceq_self p)

/-- If `A ⪯ B`, then `chain_attestations A ⊆ chain_attestations B`. -/
theorem chain_attestations_mono {A B : Block V} (h : Block.preceq A B = true) :
    chain_attestations A ⊆ chain_attestations B := by
  induction B with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h
      subst h
      exact Finset.Subset.refl _
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | h
      · exact Finset.Subset.refl _
      · exact (ih h).trans (by
          simp only [chain_attestations]
          exact Finset.subset_union_right)

/-- A block's own attestations are among its chain attestations. -/
theorem mem_chain_attestations_of_mem {p : Block V} {s : Slot} {r : BlockId}
    {gv gsv : List (GoldfishVote V)} {ats : List (CombinedAttestation V)}
    {a : CombinedAttestation V} (ha : a ∈ ats) :
    a ∈ chain_attestations (Block.node p s r gv gsv ats i) := by
  simp only [chain_attestations]
  exact Finset.mem_union_left _ (List.mem_toFinset.mpr ha)

end Structural

/-! ## `process_attestation`, field by field -/

section Attestations

variable {V : Type} [DecidableEq V] {σ : ChainState V} {a : CombinedAttestation V}

/-- `process_attestation` keeps the fields `L`, `h`, `T_h`, `J`, `h_j`, `F` and `h_F`. -/
theorem process_attestation_fields (σ : ChainState V) (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).L = σ.L ∧
      (Protocol.process_attestation σ a).h = σ.h ∧
      (Protocol.process_attestation σ a).T_h = σ.T_h ∧
      (Protocol.process_attestation σ a).J = σ.J ∧
      (Protocol.process_attestation σ a).h_j = σ.h_j ∧
      (Protocol.process_attestation σ a).F = σ.F ∧
      (Protocol.process_attestation σ a).h_F = σ.h_F := by
  unfold Protocol.process_attestation
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `process_attestation` adds the signer to `target_participation` exactly when the attestation's
    height pair is the target `(σ.h, σ.T_h.root)`. -/
theorem process_attestation_target_participation (σ : ChainState V)
    (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).target_participation =
      if a.height_pair = HeightPair.target σ.h σ.T_h.root then
        insert a.val_index σ.target_participation
      else σ.target_participation := by
  unfold Protocol.process_attestation
  split_ifs <;> rfl

/-- `process_attestation` adds the signer to `progress` when the attestation's height pair is the
    target `(σ.h, σ.T_h.root)` or a timeout at `σ.h`. -/
theorem process_attestation_progress (σ : ChainState V)
    (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).progress =
      if a.height_pair = HeightPair.target σ.h σ.T_h.root then
        insert a.val_index σ.progress
      else if a.height_pair = HeightPair.timeout σ.h then
        insert a.val_index σ.progress
      else σ.progress := by
  unfold Protocol.process_attestation
  split_ifs <;> rfl

/-- `process_attestation` adds the signer to `finalize` exactly when `σ.h_F < σ.h_j` and the
    attestation's finality pair is `(σ.h_j, σ.J.root)`. -/
theorem process_attestation_finalize (σ : ChainState V)
    (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).finalize =
      if decide (σ.h_F < σ.h_j) &&
          decide (a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) then
        insert a.val_index σ.finalize
      else σ.finalize := by
  unfold Protocol.process_attestation
  split_ifs <;> rfl


/-- A member of `finalize` after `process_attestation` was already a member, or is the signer and
    its finality pair is `(σ.h_j, σ.J.root)`. -/
theorem mem_finalize_process_attestation {i : V}
    (h : i ∈ (Protocol.process_attestation σ a).finalize) :
    i ∈ σ.finalize ∨
      (i = a.val_index ∧ a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) := by
  rw [process_attestation_finalize] at h
  split_ifs at h with h1
  · rcases Finset.mem_insert.mp h with rfl | h
    · refine Or.inr ⟨rfl, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.2
    · exact Or.inl h
  · exact Or.inl h


end Attestations


/-! ## `advance_height` and the finality write -/

section Advance

variable {V : Type} {cfg : HeightConfig} {σ : ChainState V}

/-- `advance_height` increments the height. -/
theorem advance_height_h : (Protocol.advance_height cfg σ).h = σ.h + 1 := rfl

/-- `advance_height` sets `T_h` to the latest block `L`. -/
theorem advance_height_T_h : (Protocol.advance_height cfg σ).T_h = σ.L := rfl

/-- `advance_height` clears `target_participation`. -/
theorem advance_height_target_participation :
    (Protocol.advance_height cfg σ).target_participation = ∅ := rfl

/-- `advance_height` clears `progress`. -/
theorem advance_height_progress :
    (Protocol.advance_height cfg σ).progress = ∅ := rfl


/-- `advance_height` keeps the justified block `J`. -/
theorem advance_height_J : (Protocol.advance_height cfg σ).J = σ.J := rfl

/-- `advance_height` keeps the justification height `h_j`. -/
theorem advance_height_h_j : (Protocol.advance_height cfg σ).h_j = σ.h_j := rfl


end Advance

section HeightEvents

variable {V : Type} [DecidableEq V] [Fintype V] {σ : ChainState V}

/-- The state `process_height_events` reaches after its finality branch and before its two height
    branches: `F` and `h_F` set to `J` and `h_j` when `finalityReady` holds, `σ` otherwise. -/
def afterFin (E : Env V) (σ : ChainState V) : ChainState V :=
  if Protocol.finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ

variable (E : Env V)

/-- The finality branch keeps the height. -/
theorem afterFin_h : (afterFin E σ).h = σ.h := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps the height target `T_h`. -/
theorem afterFin_T_h : (afterFin E σ).T_h = σ.T_h := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps the latest block `L`. -/
theorem afterFin_L : (afterFin E σ).L = σ.L := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps the justified block `J`. -/
theorem afterFin_J : (afterFin E σ).J = σ.J := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps the justification height `h_j`. -/
theorem afterFin_h_j : (afterFin E σ).h_j = σ.h_j := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps `target_participation`. -/
theorem afterFin_target_participation :
    (afterFin E σ).target_participation = σ.target_participation := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps `progress`. -/
theorem afterFin_progress : (afterFin E σ).progress = σ.progress := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps `finalize`. -/
theorem afterFin_finalize : (afterFin E σ).finalize = σ.finalize := by
  unfold afterFin; split_ifs <;> rfl

/-- The finality branch keeps `nj`. -/
theorem afterFin_nj : (afterFin E σ).nj = σ.nj := by
  unfold afterFin; split_ifs <;> rfl

/-- `process_height_events` as its finality branch `afterFin` followed by the justification branch,
    the progress branch, or neither. -/
theorem process_height_events_eq (cfg : HeightConfig) (σ : ChainState V) :
    Protocol.process_height_events E cfg σ =
      if Protocol.targetReady E (afterFin E σ) then
        Protocol.advance_height cfg
          { afterFin E σ with
            J := (afterFin E σ).T_h
            h_j := (afterFin E σ).h
            finalize := ∅ }
      else if Protocol.progReady E cfg (afterFin E σ) then
        Protocol.advance_height cfg (afterFin E σ)
      else afterFin E σ := rfl

/-- The finalized block after `process_height_events` is the one `afterFin` writes: neither height
    branch writes `F`. -/
theorem process_height_events_F (cfg : HeightConfig) (σ : ChainState V) :
    (Protocol.process_height_events E cfg σ).F = (afterFin E σ).F := by
  rw [process_height_events_eq]
  split_ifs <;> rfl

/-- The finalized height after `process_height_events` is the one `afterFin` writes. -/
theorem process_height_events_h_F (cfg : HeightConfig) (σ : ChainState V) :
    (Protocol.process_height_events E cfg σ).h_F = (afterFin E σ).h_F := by
  rw [process_height_events_eq]
  split_ifs <;> rfl

/-- `afterFin` sets `F` to `J` when `finalityReady` holds, and keeps it otherwise. -/
theorem afterFin_F : (afterFin E σ).F =
    if Protocol.finalityReady E σ then σ.J else σ.F := by
  unfold afterFin; split_ifs <;> rfl

/-- `afterFin` sets `h_F` to `h_j` when `finalityReady` holds, and keeps it otherwise. -/
theorem afterFin_h_F : (afterFin E σ).h_F =
    if Protocol.finalityReady E σ then σ.h_j else σ.h_F := by
  unfold afterFin; split_ifs <;> rfl

/-! ### The three readiness tests as quorum facts -/

/-- `finalityReady` gives a quorum on `finalize`. -/
theorem isQuorum_of_finalityReady (h : Protocol.finalityReady E σ = true) :
    E.electorate.IsQuorum σ.finalize := by
  simp only [Protocol.finalityReady, Bool.and_eq_true,
    ChainState.finalityQuorum, Electorate.quorumCheck, decide_eq_true_eq] at h
  exact h.2

/-- `finalityReady` gives `h_F < h_j`. -/
theorem lt_of_finalityReady (h : Protocol.finalityReady E σ = true) :
    σ.h_F < σ.h_j := by
  simp only [Protocol.finalityReady, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- `targetReady` gives a quorum on `target_participation`. -/
theorem isQuorum_of_targetReady (h : Protocol.targetReady E σ = true) :
    E.electorate.IsQuorum σ.target_participation := by
  simp only [Protocol.targetReady, Bool.and_eq_true, ChainState.targetQuorum,
    Electorate.quorumCheck, decide_eq_true_eq] at h
  exact h.2

/-- `progReady` gives a quorum on `target_participation`, or a quorum on `progress` once
    `T_h.slot + timeoutDelay ≤ s`. -/
theorem quorum_of_progReady (cfg : HeightConfig)
    (h : Protocol.progReady E cfg σ = true) :
    E.electorate.IsQuorum σ.target_participation ∨
      (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s ∧
        E.electorate.IsQuorum σ.progress) := by
  simp only [Protocol.progReady, Bool.or_eq_true, Bool.and_eq_true,
    ChainState.targetQuorum, ChainState.progQuorum, Electorate.quorumCheck,
    decide_eq_true_eq] at h
  exact h

end HeightEvents


/-! ## The ancestry chain `F ⪯ J ⪯ T_h ⪯ L` -/

section Order

variable {V : Type} [DecidableEq V]

/-- The ancestry-and-height invariant of a chain state: `F ⪯ J ⪯ T_h ⪯ L`, `h_F ≤ h_j` and
    `h_j < h`. -/
structure ChainOrder (σ : ChainState V) : Prop where
  /-- `T_h ⪯ L`. -/
  target_preceq_latest : Block.preceq σ.T_h σ.L = true
  /-- `J ⪯ T_h`. -/
  justified_preceq_target : Block.preceq σ.J σ.T_h = true
  /-- `F ⪯ J`. -/
  finalized_preceq_justified : Block.preceq σ.F σ.J = true
  /-- `h_F ≤ h_j`. -/
  heights_ordered : σ.h_F ≤ σ.h_j
  /-- `h_j < h`. -/
  justified_below_height : σ.h_j < σ.h

/-- The finalized block is an ancestor of the latest block: `F ⪯ L`. -/
theorem ChainOrder.finalized_preceq_latest {σ : ChainState V} (h : ChainOrder σ) :
    Block.preceq σ.F σ.L = true :=
  Block.preceq_trans h.finalized_preceq_justified
    (Block.preceq_trans h.justified_preceq_target h.target_preceq_latest)

/-- `h_F < h`. -/
theorem ChainOrder.finalized_below_height {σ : ChainState V} (h : ChainOrder σ) :
    σ.h_F < σ.h :=
  Nat.lt_of_le_of_lt h.heights_ordered h.justified_below_height

/-- The initial chain state satisfies `ChainOrder`. -/
theorem chainOrder_initial : ChainOrder (ChainState.initial : ChainState V) :=
  { target_preceq_latest := Block.preceq_self _
    justified_preceq_target := Block.preceq_self _
    finalized_preceq_justified := Block.preceq_self _
    heights_ordered := Nat.le_refl 0
    justified_below_height := Nat.zero_lt_one }


variable [Fintype V]

/-- The finality branch `afterFin` preserves `ChainOrder`. -/
theorem chainOrder_afterFin (E : Env V) {σ : ChainState V} (h : ChainOrder σ) :
    ChainOrder (afterFin E σ) := by
  unfold afterFin
  split_ifs
  · exact
      { target_preceq_latest := h.target_preceq_latest
        justified_preceq_target := h.justified_preceq_target
        finalized_preceq_justified := Block.preceq_self _
        heights_ordered := Nat.le_refl _
        justified_below_height := h.justified_below_height }
  · exact h

/-- `process_height_events` preserves `ChainOrder`. -/
theorem chainOrder_process_height_events (E : Env V) (cfg : HeightConfig)
    {σ : ChainState V} (h : ChainOrder σ) :
    ChainOrder (Protocol.process_height_events E cfg σ) := by
  have h' := chainOrder_afterFin E h
  rw [process_height_events_eq]
  split_ifs
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target := h'.target_preceq_latest
        finalized_preceq_justified :=
          Block.preceq_trans h'.finalized_preceq_justified h'.justified_preceq_target
        heights_ordered := Nat.le_of_lt h'.finalized_below_height
        justified_below_height := Nat.lt_succ_self _ }
  · exact
      { target_preceq_latest := Block.preceq_self _
        justified_preceq_target :=
          Block.preceq_trans h'.justified_preceq_target h'.target_preceq_latest
        finalized_preceq_justified := h'.finalized_preceq_justified
        heights_ordered := h'.heights_ordered
        justified_below_height := Nat.lt_succ_of_lt h'.justified_below_height }
  · exact h'


end Order

end Protocol
end DecoupledConsensusModel

end
