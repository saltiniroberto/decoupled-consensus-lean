module
public import GoldilocksCorrectness.Statements.Routines.CertificateDefs
public import GoldilocksCorrectness.Proofs.Routines.ChainStateFields
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
import all Goldilocks.Config
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# The certificates of a chain state

The proofs of the statements of
`GoldilocksCorrectness/Statements/Routines/CertificateStatements.lean`: quorum intersection
(Lemma 65), the certificates behind a chain state (Lemma 66), and the first advance past a height
(Lemma 67); and the justification behind a finalization (`justification_witness_of_finalized`:
a chain that finalized a block passed through a state that had just justified it).

The route: `ParticipationWitnessed P σ` carries every counted validator of `σ` back to an
attestation satisfying `P`; `ChainCertified C B σ` bundles it, at `P := (on_chain · B)`, with
the pending justifications, the justification and the finalization of `σ` and their certificates
on the chain of `B`. The bundle holds of every block's chain state, by induction on the block:
counting the block's attestations keeps it (`chainCertified_process_attestations`), and so do the
height events (`chainCertified_process_height_events`).
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn FinalityCertOn)
open GoldilocksCorrectness.Proofs.Routines (chainStateOf_node chainStateOf_bounds
  chainStateOf_height chainStateOf_T_h_spec chainStateOf_J_spec)

variable {V : Type} [DecidableEq V]

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Inclusion on a chain -/

/-- An attestation included on the parent's chain is included on the block's chain. -/
theorem on_chain_node_of_parent (a : Attestation V) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V)
    -- `a` is included on the parent's chain
    (h : on_chain a p = true) : on_chain a (.node p s r votes support ats v) = true := by
  simp only [on_chain, attestations_on_chain, decide_eq_true_eq, List.mem_append] at h ⊢
  exact Or.inr h

/-- An attestation the block includes is included on the block's chain. -/
theorem on_chain_node_of_mem (a : Attestation V) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V)
    -- the block includes `a`
    (h : a ∈ ats) : on_chain a (.node p s r votes support ats v) = true := by
  simp only [on_chain, attestations_on_chain, decide_eq_true_eq, List.mem_append]
  exact Or.inl h

variable [Fintype V]

/-- A justification certificate on the chain of `B` is one on the chain of every block whose
chain includes `B`'s attestations. -/
theorem justificationCertOn_mono {B B' : Block V} {h : Height} {T : Block V}
    -- every attestation included on `B`'s chain is included on `B'`'s
    (hmono : ∀ a : Attestation V, on_chain a B = true → on_chain a B' = true)
    -- the certificate on `B`'s chain
    (hc : JustificationCertOn B h T) : JustificationCertOn B' h T := by
  obtain ⟨A, hA, hv⟩ := hc
  refine ⟨A, hA, fun v hvA => ?_⟩
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := hv v hvA
  exact ⟨a, h1, h2, h3, h4, hmono a h5⟩

/-- A finality certificate on the chain of `B` is one on the chain of every block whose chain
includes `B`'s attestations. -/
theorem finalityCertOn_mono {B B' : Block V} {h : Height} {T : Block V}
    -- every attestation included on `B`'s chain is included on `B'`'s
    (hmono : ∀ a : Attestation V, on_chain a B = true → on_chain a B' = true)
    -- the certificate on `B`'s chain
    (hc : FinalityCertOn B h T) : FinalityCertOn B' h T := by
  obtain ⟨A, hA, hv⟩ := hc
  refine ⟨A, hA, fun v hvA => ?_⟩
  obtain ⟨a, h1, h2, h3⟩ := hv v hvA
  exact ⟨a, h1, h2, hmono a h3⟩

/-! ## The witnesses of the participation sets -/

/-- Every validator a chain state counts has an attestation satisfying `P` that it was counted
for. -/
structure ParticipationWitnessed (P : Attestation V → Prop) (σ : ChainState V) : Prop where
  /-- Every validator of the target participation has a target vote at `σ.h` naming `σ.T_h`. -/
  target : ∀ v ∈ σ.target_participation, ∃ a : Attestation V, P a ∧ a.val_index = v ∧
    a.h = σ.h ∧ a.T = σ.T_h.root ∧ a.τ = false
  /-- Every validator of the progress set has a vote at `σ.h` naming `σ.T_h`. -/
  progress : ∀ v ∈ σ.progress, ∃ a : Attestation V, P a ∧ a.val_index = v ∧
    a.h = σ.h ∧ a.T = σ.T_h.root
  /-- Every validator of the finality participation of a pending justification `e` has an
  attestation with the finality pair `(e.j, e.T.root)`. -/
  finality : ∀ e ∈ σ.pending_finality, ∀ v ∈ σ.finality_participation e.j,
    ∃ a : Attestation V, P a ∧ a.val_index = v ∧ a.finality_pair = some ⟨e.j, e.T.root⟩

omit [DecidableEq V] [Fintype V] in
/-- Two pending justifications of a list in strictly increasing order of heights, at one height,
are one. -/
theorem eq_of_pairwise_j {l : List (PendingPair V)}
    -- the heights of `l` are strictly increasing
    (hl : l.Pairwise (fun e e' => e.j < e'.j))
    {e e' : PendingPair V}
    -- both are in `l`, at one height
    (he : e ∈ l) (he' : e' ∈ l) (hj : e.j = e'.j) : e = e' := by
  induction l with
  | nil => exact absurd he List.not_mem_nil
  | cons x l ih =>
      rw [List.pairwise_cons] at hl
      rcases List.mem_cons.mp he with h1 | h1 <;> rcases List.mem_cons.mp he' with h2 | h2
      · exact h1.trans h2.symm
      · have := hl.1 e' h2; rw [h1] at hj; omega_nat
      · have := hl.1 e h1; rw [h2] at hj; omega_nat
      · exact ih hl.2 h1 h2

omit [Fintype V] in
/-- The witnesses survive counting one attestation satisfying `P`, when the pending heights are
strictly increasing. -/
theorem witnessed_process_attestation (P : Attestation V → Prop) (σ : ChainState V)
    (a : Attestation V)
    -- the attestation counted satisfies `P`
    (hP : P a)
    -- the pending justifications are in strictly increasing order of heights
    (hs : σ.pending_finality.Pairwise (fun e e' => e.j < e'.j))
    -- the witnesses before
    (hw : ParticipationWitnessed P σ) :
    ParticipationWitnessed P (process_attestation σ a) := by
  obtain ⟨tp, pr, fp, heq, -⟩ := process_attestation_eq σ a
  have hh : (process_attestation σ a).h = σ.h := by rw [heq]
  have hT : (process_attestation σ a).T_h = σ.T_h := by rw [heq]
  have hpend : (process_attestation σ a).pending_finality = σ.pending_finality := by rw [heq]
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun e he v hv => ?_⟩
  · rw [hh, hT]
    rcases process_attestation_target_mem σ a v hv with hv | ⟨rfl, h1, h2, h3⟩
    · exact hw.target v hv
    · exact ⟨a, hP, rfl, h1, h2, h3⟩
  · rw [hh, hT]
    rcases process_attestation_progress_mem σ a v hv with hv | ⟨rfl, h1, h2⟩
    · exact hw.progress v hv
    · exact ⟨a, hP, rfl, h1, h2⟩
  · rw [hpend] at he
    rcases process_attestation_finality_mem σ a e.j v hv with hv | ⟨rfl, p, hp, hpj, hpend'⟩
    · exact hw.finality e he v hv
    · simp only [is_pending, decide_eq_true_eq] at hpend'
      obtain ⟨e', he', hj', hT'⟩ := hpend'
      have hee : e' = e := eq_of_pairwise_j hs he' he (hj'.trans hpj)
      subst hee
      refine ⟨a, hP, rfl, ?_⟩
      rw [hp]
      cases p
      simp_all

omit [Fintype V] in
/-- The witnesses survive counting the attestations of a block, when each satisfies `P` and the
pending heights are strictly increasing.

The variables:
- `P`: the condition on the witnessing attestations; `σ`: the parent's chain state; `B`: the
  block. -/
theorem witnessed_process_attestations (P : Attestation V → Prop) (σ : ChainState V)
    (B : Block V)
    -- every attestation of `B` satisfies `P`
    (hP : ∀ a ∈ B.attestations, P a)
    -- the pending justifications are in strictly increasing order of heights
    (hs : σ.pending_finality.Pairwise (fun e e' => e.j < e'.j))
    -- the witnesses before
    (hw : ParticipationWitnessed P σ) :
    ParticipationWitnessed P (process_attestations σ B B.attestations) := by
  have hfold : ParticipationWitnessed P
        (B.attestations.foldl process_attestation { σ with s := B.slot }) ∧
      (B.attestations.foldl process_attestation { σ with s := B.slot }).pending_finality =
        σ.pending_finality := by
    refine foldl_process_attestation_inv
      (fun σ' => ParticipationWitnessed P σ' ∧ σ'.pending_finality = σ.pending_finality)
      B.attestations _ ⟨⟨hw.target, hw.progress, hw.finality⟩, rfl⟩ ?_
    rintro a ha σ' ⟨hw', hp'⟩
    obtain ⟨tp, pr, fp, heq, -⟩ := process_attestation_eq σ' a
    refine ⟨witnessed_process_attestation P σ' a (hP a ha) (hp' ▸ hs) hw', ?_⟩
    rw [heq]
    exact hp'
  rw [process_attestations_eq_foldl]
  exact ⟨hfold.1.target, hfold.1.progress, hfold.1.finality⟩

/-! ## The bundle -/

/-- What the chain state `σ` holds for the chain of `B`: its pending justifications, its
justification and its finalization, with their certificates on the chain of `B`, and the
witnesses of its participation sets. -/
structure ChainCertified (C : Config) (B : Block V) (σ : ChainState V) : Prop where
  /-- The pending justifications are in strictly increasing order of heights. -/
  sorted : σ.pending_finality.Pairwise (fun e e' => e.j < e'.j)
  /-- Every pending justification names a block of the chain of `B`. -/
  pendingAnc : ∀ e ∈ σ.pending_finality, e.T.AncestorEq B
  /-- Every pending justification names a block whose chain state is at its height. -/
  pendingHeight : ∀ e ∈ σ.pending_finality, (chainStateOf C e.T).h = e.j
  /-- Every pending justification has a justification certificate on the chain of `B`. -/
  pendingCert : ∀ e ∈ σ.pending_finality, JustificationCertOn B e.j e.T
  /-- Every counted validator has its attestation included on the chain of `B`. -/
  witnessed : ParticipationWitnessed (fun a => on_chain a B = true) σ
  /-- The justification has a justification certificate on the chain of `B`. -/
  justified : 1 ≤ σ.h_j → JustificationCertOn B σ.h_j σ.J
  /-- The finalization has a justification and a finality certificate on the chain of `B`, and
  names a block of that chain whose chain state is at its height. -/
  finalized : 1 ≤ σ.h_F →
    JustificationCertOn B σ.h_F σ.F ∧ FinalityCertOn B σ.h_F σ.F ∧ σ.F.AncestorEq B ∧
      (chainStateOf C σ.F).h = σ.h_F

/-- The genesis block's chain state is certified. -/
theorem chainCertified_genesis (C : Config) :
    ChainCertified C (Block.genesis : Block V) (chainStateOf C Block.genesis) := by
  refine ⟨List.Pairwise.nil, fun e he => absurd he List.not_mem_nil,
    fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil,
    ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
      fun e he => absurd he List.not_mem_nil⟩, fun h => ?_, fun h => ?_⟩
  · exact absurd h (show ¬ (1 : Nat) ≤ 0 by decide)
  · exact absurd h (show ¬ (1 : Nat) ≤ 0 by decide)

/-- Counting the attestations of a block `B` keeps the bundle, moved from the chain of `B`'s
parent `p` to the chain of `B`.

The variables:
- `C`: the parameters; `p`: the parent; `B`: the block; `σ`: the parent's chain state. -/
theorem chainCertified_process_attestations (C : Config) (p B : Block V) (σ : ChainState V)
    -- `p` is an ancestor of `B`
    (hpB : p.AncestorEq B)
    -- every attestation included on `p`'s chain is included on `B`'s
    (hmono : ∀ a : Attestation V, on_chain a p = true → on_chain a B = true)
    -- every attestation of `B` is included on `B`'s chain
    (hatt : ∀ a ∈ B.attestations, on_chain a B = true)
    -- the bundle for the parent
    (hc : ChainCertified C p σ) :
    ChainCertified C B (process_attestations σ B B.attestations) := by
  have hw := witnessed_process_attestations (fun a => on_chain a B = true) σ B hatt hc.sorted
    ⟨fun v hv => (hc.witnessed.target v hv).imp fun a h => ⟨hmono a h.1, h.2⟩,
      fun v hv => (hc.witnessed.progress v hv).imp fun a h => ⟨hmono a h.1, h.2⟩,
      fun e he v hv => (hc.witnessed.finality e he v hv).imp fun a h => ⟨hmono a h.1, h.2⟩⟩
  obtain ⟨tp, pr, fp, heq, -⟩ := process_attestations_eq σ B B.attestations
  rw [heq] at hw ⊢
  refine ⟨hc.sorted, fun e he => ancestorEq_trans (hc.pendingAnc e he) hpB, hc.pendingHeight,
    fun e he => justificationCertOn_mono hmono (hc.pendingCert e he), hw,
    fun h => justificationCertOn_mono hmono (hc.justified h), fun h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hc.finalized h
  exact ⟨justificationCertOn_mono hmono h1, finalityCertOn_mono hmono h2,
    ancestorEq_trans h3 hpB, h4⟩

/-- A quorum of the target participation is a justification certificate on the chain of `B` for
the chain state's height and `T_h`. -/
theorem justificationCertOn_of_target (B : Block V) (σ : ChainState V)
    -- every counted validator has its attestation included on `B`'s chain
    (hw : ParticipationWitnessed (fun a => on_chain a B = true) σ)
    -- the target participation is a quorum
    (hq : quorum V ≤ σ.target_participation.card) :
    JustificationCertOn B σ.h σ.T_h := by
  refine ⟨σ.target_participation, hq, fun v hv => ?_⟩
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := hw.target v hv
  exact ⟨a, h2, h3, h4, h5, h1⟩

/-- The finalization the loop over the pending justifications leaves is certified: it is the
chain state's own, or a pending justification whose finality participation is a quorum. -/
theorem finalized_of_loop (C : Config) (B : Block V) (σ : ChainState V) (F' : Block V)
    (h_F' : Height)
    -- the bundle for `σ`
    (hc : ChainCertified C B σ)
    -- what the loop leaves: `σ`'s own finalization, or a pending justification with a quorate
    -- finality participation
    (hF' : (F' = σ.F ∧ h_F' = σ.h_F) ∨
      ∃ e ∈ σ.pending_finality, F' = e.T ∧ h_F' = e.j ∧
        quorum V ≤ (σ.finality_participation e.j).card) :
    1 ≤ h_F' → JustificationCertOn B h_F' F' ∧ FinalityCertOn B h_F' F' ∧ F'.AncestorEq B ∧
      (chainStateOf C F').h = h_F' := by
  intro h1
  rcases hF' with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl, hq⟩
  · exact hc.finalized h1
  · refine ⟨hc.pendingCert e he, ⟨σ.finality_participation e.j, hq, fun v hv => ?_⟩,
      hc.pendingAnc e he, hc.pendingHeight e he⟩
    obtain ⟨a, h1, h2, h3⟩ := hc.witnessed.finality e he v hv
    exact ⟨a, h2, h3, h1⟩

/-- The height events keep the bundle, when the chain state's justification height is less than
its height, every pending justification is at a height at most the justification height, and its
`T_h` is a block of the chain of `B` whose chain state is at its height.

The variables:
- `C`: the parameters; `B`: the block; `σ`: the chain state after `B`'s attestations are
  counted. -/
theorem chainCertified_process_height_events (C : Config) (B : Block V) (σ : ChainState V)
    -- the justification height is less than the height
    (hjh : σ.h_j < σ.h)
    -- every pending justification is at a height at most the justification height
    (hle : ∀ e ∈ σ.pending_finality, e.j ≤ σ.h_j)
    -- `σ.T_h` is a block of `B`'s chain
    (hTanc : σ.T_h.AncestorEq B)
    -- `σ.T_h`'s chain state is at the height `σ.h`
    (hTh : (chainStateOf C σ.T_h).h = σ.h)
    -- the bundle before the height events
    (hc : ChainCertified C B σ) :
    ChainCertified C B (process_height_events C σ) := by
  obtain ⟨F', h_F', hF', hb⟩ := process_height_events_branches C σ
  have hfin := finalized_of_loop C B σ F' h_F' hc hF'
  have hfilt : ∀ e ∈ σ.pending_finality.filter (fun e => decide (h_F' < e.j)),
      e ∈ σ.pending_finality := fun e he => (List.mem_filter.mp he).1
  have hsfilt : (σ.pending_finality.filter (fun e => decide (h_F' < e.j))).Pairwise
      (fun e e' => e.j < e'.j) := hc.sorted.sublist List.filter_sublist
  rcases hb with ⟨hq, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR]
  · -- the justification branch
    rw [advance_height_eq]
    have hmem : ∀ e ∈ newest C.K_W (σ.pending_finality.filter (fun e => decide (h_F' < e.j)) ++
          [PendingPair.mk σ.h σ.T_h]),
        e ∈ σ.pending_finality ∨ e = PendingPair.mk σ.h σ.T_h := by
      intro e he
      rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
      · exact Or.inl (hfilt e he)
      · exact Or.inr (List.mem_singleton.mp he)
    refine ⟨?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, ⟨?_, ?_, fun e he v hv => ?_⟩,
      fun _ => justificationCertOn_of_target B σ hc.witnessed hq, hfin⟩
    · refine List.Pairwise.sublist (List.drop_sublist _ _) ?_
      refine List.pairwise_append.mpr ⟨hsfilt, List.pairwise_singleton _ _, ?_⟩
      intro e he e' he'
      rw [List.mem_singleton.mp he']
      have := hle e (hfilt e he)
      omega_nat
    · rcases hmem e he with he | rfl
      · exact hc.pendingAnc e he
      · exact hTanc
    · rcases hmem e he with he | rfl
      · exact hc.pendingHeight e he
      · exact hTh
    · rcases hmem e he with he | rfl
      · exact hc.pendingCert e he
      · exact justificationCertOn_of_target B σ hc.witnessed hq
    · intro v hv; exact absurd hv (Finset.notMem_empty v)
    · intro v hv; exact absurd hv (Finset.notMem_empty v)
    · rcases hmem e he with he | rfl
      · have hne : e.j ≠ σ.h := by have := hle e he; omega_nat
        change v ∈ Function.update σ.finality_participation σ.h ∅ e.j at hv
        rw [Function.update_of_ne hne] at hv
        exact hc.witnessed.finality e he v hv
      · change v ∈ Function.update σ.finality_participation σ.h ∅ σ.h at hv
        rw [Function.update_self] at hv
        exact absurd hv (Finset.notMem_empty v)
  · -- the timeout branch
    rw [advance_height_eq]
    exact ⟨hsfilt, fun e he => hc.pendingAnc e (hfilt e he),
      fun e he => hc.pendingHeight e (hfilt e he), fun e he => hc.pendingCert e (hfilt e he),
      ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
        fun e he v hv => hc.witnessed.finality e (hfilt e he) v hv⟩, hc.justified, hfin⟩
  · -- neither
    exact ⟨hsfilt, fun e he => hc.pendingAnc e (hfilt e he),
      fun e he => hc.pendingHeight e (hfilt e he), fun e he => hc.pendingCert e (hfilt e he),
      ⟨hc.witnessed.target, hc.witnessed.progress,
        fun e he v hv => hc.witnessed.finality e (hfilt e he) v hv⟩, hc.justified, hfin⟩

/-- Every block's chain state is certified for the block's chain.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem chainCertified_chainStateOf (C : Config) (B : Block V) :
    ChainCertified C B (chainStateOf C B) := by
  induction B with
  | genesis => exact chainCertified_genesis C
  | node p s r votes support ats v ih =>
      have hpB : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have h1 := chainCertified_process_attestations C p (.node p s r votes support ats v)
        (chainStateOf C p) hpB (fun a h => on_chain_node_of_parent a p s r votes support ats v h)
        (fun a h => on_chain_node_of_mem a p s r votes support ats v h) ih
      obtain ⟨tp, pr, fp, heq, -⟩ := process_attestations_eq (chainStateOf C p)
        (.node p s r votes support ats v) (Block.node p s r votes support ats v).attestations
      obtain ⟨-, hjh, -, hle⟩ := chainStateOf_bounds C p
      obtain ⟨hTanc, hTh⟩ := chainStateOf_T_h_spec C p
      rw [chainStateOf_node, state_transition_eq]
      refine chainCertified_process_height_events C _ _ ?_ ?_ ?_ ?_ h1 <;> rw [heq]
      · exact hjh
      · exact hle
      · exact ancestorEq_trans hTanc hpB
      · exact hTh

/-! ## The justification behind a finalization -/

/-- Every pending justification of a block's chain state, and its finalization when the
finalization height is at least `1`, was justified by a block of the block's chain: some block
`Y`, `B` or an ancestor of `B`, has a chain state whose justification height and justified block
are the pair's.

Why: a pending pair is appended exactly in the justification branch of the height events, which
writes the same pair as the chain state's justification; the finalization is the chain state's
own or a pending pair. By induction on the block.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem justificationWitnessed_chainStateOf (C : Config) (B : Block V) :
    (∀ e ∈ (chainStateOf C B).pending_finality, ∃ Y : Block V, Y.AncestorEq B ∧
      (chainStateOf C Y).h_j = e.j ∧ (chainStateOf C Y).J = e.T) ∧
    (1 ≤ (chainStateOf C B).h_F → ∃ Y : Block V, Y.AncestorEq B ∧
      (chainStateOf C Y).h_j = (chainStateOf C B).h_F ∧
      (chainStateOf C Y).J = (chainStateOf C B).F) := by
  induction B with
  | genesis =>
      exact ⟨fun e he => absurd he List.not_mem_nil,
        fun h => absurd h (show ¬ (1 : Nat) ≤ 0 by decide)⟩
  | node p s r votes support ats v ih =>
      have hpB : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have hBB : (Block.node p s r votes support ats v).AncestorEq
          (.node p s r votes support ats v) := ancestorEq_refl _
      have hst : chainStateOf C (.node p s r votes support ats v) =
          process_height_events C (process_attestations (chainStateOf C p)
            (.node p s r votes support ats v)
            (Block.node p s r votes support ats v).attestations) := by
        rw [chainStateOf_node, state_transition_eq]
      obtain ⟨σ, hσ⟩ : ∃ σ : ChainState V, process_attestations (chainStateOf C p)
          (.node p s r votes support ats v)
          (Block.node p s r votes support ats v).attestations = σ := ⟨_, rfl⟩
      obtain ⟨tp, pr, fp, heq, -⟩ := process_attestations_eq (chainStateOf C p)
        (.node p s r votes support ats v) (Block.node p s r votes support ats v).attestations
      have hpf : σ.pending_finality = (chainStateOf C p).pending_finality := by
        rw [← hσ, heq]
      have hσF : σ.F = (chainStateOf C p).F := by rw [← hσ, heq]
      have hσhF : σ.h_F = (chainStateOf C p).h_F := by rw [← hσ, heq]
      rw [hσ] at hst
      obtain ⟨F', h_F', hF', hb⟩ := process_height_events_branches C σ
      rw [hpf, hσF, hσhF] at hF'
      -- what the loop leaves for the finalization is witnessed
      have hfin : 1 ≤ h_F' → ∃ Y : Block V, Y.AncestorEq (.node p s r votes support ats v) ∧
          (chainStateOf C Y).h_j = h_F' ∧ (chainStateOf C Y).J = F' := by
        intro h1
        rcases hF' with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl, -⟩
        · obtain ⟨Y, hY, h2, h3⟩ := ih.2 h1
          exact ⟨Y, ancestorEq_trans hY hpB, h2, h3⟩
        · obtain ⟨Y, hY, h2, h3⟩ := ih.1 e he
          exact ⟨Y, ancestorEq_trans hY hpB, h2, h3⟩
      have hold : ∀ e ∈ σ.pending_finality.filter (fun e => decide (h_F' < e.j)),
          ∃ Y : Block V, Y.AncestorEq (.node p s r votes support ats v) ∧
            (chainStateOf C Y).h_j = e.j ∧ (chainStateOf C Y).J = e.T := by
        intro e he
        obtain ⟨Y, hY, h2, h3⟩ := ih.1 e (hpf ▸ (List.mem_filter.mp he).1)
        exact ⟨Y, ancestorEq_trans hY hpB, h2, h3⟩
      rcases hb with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] at hst
      · -- the justification branch: the new pair is the block's own justification
        refine ⟨fun e he => ?_, fun h1 => ?_⟩
        · rw [hst] at he
          rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
          · exact hold e he
          · rw [List.mem_singleton.mp he]
            exact ⟨_, hBB, by rw [hst]; rfl, by rw [hst]; rfl⟩
        · rw [hst] at h1 ⊢
          exact hfin h1
      · refine ⟨fun e he => ?_, fun h1 => ?_⟩
        · rw [hst] at he
          exact hold e he
        · rw [hst] at h1 ⊢
          exact hfin h1
      · refine ⟨fun e he => ?_, fun h1 => ?_⟩
        · rw [hst] at he
          exact hold e he
        · rw [hst] at h1 ⊢
          exact hfin h1

/-- **The finalized block was justified by a block of the chain.** When the chain state of `D` has
finalization height at least `1`, some block `Y`, `D` or an ancestor of `D`, has a chain state
whose justification height is that finalization height and whose justified block is `D`'s
finalized block.

Why: `justificationWitnessed_chainStateOf`, its second conjunct.

The variables:
- `C`: the parameters; `D`: the block.

Read aloud: a chain that finalized `F` at `h_F` passed through a state that had just justified `F`
at `h_F`. -/
theorem justification_witness_of_finalized (C : Config) (D : Block V)
    -- the finalization height of `D`'s chain state is at least `1`
    (h1 : 1 ≤ (chainStateOf C D).h_F) :
    ∃ Y : Block V, Y.AncestorEq D ∧ (chainStateOf C Y).h_j = (chainStateOf C D).h_F ∧
      (chainStateOf C Y).J = (chainStateOf C D).F :=
  (justificationWitnessed_chainStateOf C D).2 h1

/-! ## Lemma 65, quorum intersection -/

omit [DecidableEq V] in
/-- **Lemma 65 (b), the intersection threshold.** The proof; the audited statement is in
`Statements/Routines/CertificateStatements.lean`. -/
theorem lem65b_quorum_threshold :
    validator_count V ≤ 3 * (2 * quorum V - validator_count V) ∧
      validator_count V ≤ 2 * quorum V := by
  unfold quorum
  omega

/-- **Lemma 65, quorum intersection.** The proof; the audited statement is in
`Statements/Routines/CertificateStatements.lean`.

The variables:
- `A`, `A'`: the two quorums. -/
theorem lem65_quorum_intersection (A A' : Finset V)
    -- `A` is a quorum
    (hA : quorum V ≤ |A|)
    -- `A'` is a quorum
    (hA' : quorum V ≤ |A'|) :
    2 * quorum V - validator_count V ≤ |A ∩ A'| := by
  have hu : |A ∪ A'| ≤ validator_count V := Finset.card_le_univ _
  have hs := Finset.card_union_add_card_inter A A'
  omega

/-! ## Lemma 66, the certificates behind a chain state -/

/-- **Lemma 66, the certificates behind a chain state.** The proof; the audited statement is in
`Statements/Routines/CertificateStatements.lean`.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem lem66_chain_state_certified (C : Config) (B : Block V) :
    (1 ≤ (chainStateOf C B).h_j →
      JustificationCertOn B (chainStateOf C B).h_j (chainStateOf C B).J ∧
      (chainStateOf C B).J.AncestorEq B ∧
      (chainStateOf C (chainStateOf C B).J).h = (chainStateOf C B).h_j) ∧
    (∀ e ∈ (chainStateOf C B).pending_finality,
      JustificationCertOn B e.j e.T ∧ e.T.AncestorEq B ∧ (chainStateOf C e.T).h = e.j) ∧
    (1 ≤ (chainStateOf C B).h_F →
      JustificationCertOn B (chainStateOf C B).h_F (chainStateOf C B).F ∧
      FinalityCertOn B (chainStateOf C B).h_F (chainStateOf C B).F ∧
      (chainStateOf C B).F.AncestorEq B ∧
      (chainStateOf C (chainStateOf C B).F).h = (chainStateOf C B).h_F) := by
  have hc := chainCertified_chainStateOf C B
  obtain ⟨hJanc, -, hJh⟩ := chainStateOf_J_spec C B
  exact ⟨fun h => ⟨hc.justified h, hJanc, hJh h⟩,
    fun e he => ⟨hc.pendingCert e he, hc.pendingAnc e he, hc.pendingHeight e he⟩, hc.finalized⟩

/-! ## Lemma 67, the first advance past a height -/

/-- A block whose chain state is one height more than its parent's carries, on its chain, a
progress certificate at the parent's height for the parent's `T_h`.

The variables:
- `C`: the parameters; `p`: the parent; the rest: the block's fields. -/
theorem progressCertOn_of_advance (C : Config) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V)
    -- the block's chain state is one height more than its parent's
    (hadv : (chainStateOf C (.node p s r votes support ats v)).h = (chainStateOf C p).h + 1) :
    ProgressCertOn (.node p s r votes support ats v) (chainStateOf C p).h
      (chainStateOf C p).T_h := by
  have hpB : p.AncestorEq (.node p s r votes support ats v) :=
    (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
  have hc := chainCertified_process_attestations C p (.node p s r votes support ats v)
    (chainStateOf C p) hpB (fun a h => on_chain_node_of_parent a p s r votes support ats v h)
    (fun a h => on_chain_node_of_mem a p s r votes support ats v h)
    (chainCertified_chainStateOf C p)
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ChainState V,
      σ₁ = process_attestations (chainStateOf C p) (.node p s r votes support ats v) ats :=
    ⟨_, rfl⟩
  obtain ⟨tp, pr, fp, heq, -⟩ :=
    process_attestations_eq (chainStateOf C p) (.node p s r votes support ats v) ats
  have hw : ParticipationWitnessed
      (fun a => on_chain a (.node p s r votes support ats v) = true) σ₁ := by
    rw [hσ₁]; exact hc.witnessed
  have hh : σ₁.h = (chainStateOf C p).h := by rw [hσ₁, heq]
  have hT : σ₁.T_h = (chainStateOf C p).T_h := by rw [hσ₁, heq]
  have hB : chainStateOf C (.node p s r votes support ats v) = process_height_events C σ₁ := by
    rw [hσ₁]; rfl
  obtain ⟨F', h_F', -, hb⟩ := process_height_events_branches C σ₁
  rw [← hh, ← hT]
  rcases hb with ⟨hq, -⟩ | ⟨-, hq, -, -⟩ | ⟨-, -, hR⟩
  · refine ⟨σ₁.target_participation, hq, fun v hv => ?_⟩
    obtain ⟨a, h1, h2, h3, h4, -⟩ := hw.target v hv
    exact ⟨a, h2, h3, h4, h1⟩
  · refine ⟨σ₁.progress, hq, fun v hv => ?_⟩
    obtain ⟨a, h1, h2, h3, h4⟩ := hw.progress v hv
    exact ⟨a, h2, h3, h4, h1⟩
  · exfalso
    rw [hB, hR] at hadv
    change σ₁.h = (chainStateOf C p).h + 1 at hadv
    omega_nat

/-- **Lemma 67, the first advance past a height.** The proof; the audited statement is in
`Statements/Routines/CertificateStatements.lean`.

The variables:
- `C`: the parameters; `B`: the block; `h`: the height. -/
theorem lem67_first_advance (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (chainStateOf C Y.parent).h = h ∧ (chainStateOf C Y).h = h + 1 ∧
      (chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn Y h (chainStateOf C Y.parent).T_h := by
  induction B with
  | genesis =>
      exfalso
      have h0 : (chainStateOf C (Block.genesis : Block V)).h = 1 := rfl
      rw [h0] at hlt
      omega_nat
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have hpB : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      by_cases hp : h < (chainStateOf C p).h
      · obtain ⟨Y, hY, hY1, hY2, hY3, hY4, hY5⟩ := ih hp
        exact ⟨Y, ancestorEq_trans hY hpB, hY1, hY2, hY3, hY4, hY5⟩
      · have h2 := chainStateOf_height C _ hne
        change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
        have hadv : (chainStateOf C (.node p s r votes support ats v)).h =
            (chainStateOf C p).h + 1 := by
          rcases h2 with h2 | h2 <;> omega_nat
        have hhp : (chainStateOf C p).h = h := by omega_nat
        refine ⟨.node p s r votes support ats v, ancestorEq_refl _, hne, hhp, ?_, ?_, ?_⟩
        · rw [hadv, hhp]
        · exact ancestorEq_trans (chainStateOf_T_h_spec C p).1 hpB
        · change ProgressCertOn _ h (chainStateOf C p).T_h
          rw [← hhp]
          exact progressCertOn_of_advance C p s r votes support ats v hadv

/-- A block whose chain state is one height more than its parent's carries, on its chain, a
progress certificate at the parent's height for the parent's `T_h`; and the height was raised by
the justification branch, whose certificate is a justification certificate, or by the timeout
branch, whose test `T_h.slot + δt ≤ s` held at the block's slot `s`.

The variables:
- `C`: the parameters; `p`: the parent; the rest: the block's fields. -/
theorem progressCertOn_of_advance_cases (C : Config) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V)
    -- the block's chain state is one height more than its parent's
    (hadv : (chainStateOf C (.node p s r votes support ats v)).h = (chainStateOf C p).h + 1) :
    ProgressCertOn (.node p s r votes support ats v) (chainStateOf C p).h
        (chainStateOf C p).T_h ∧
      (JustificationCertOn (.node p s r votes support ats v) (chainStateOf C p).h
          (chainStateOf C p).T_h ∨
        (chainStateOf C p).T_h.slot + C.δt ≤ s) := by
  have hpB : p.AncestorEq (.node p s r votes support ats v) :=
    (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
  have hc := chainCertified_process_attestations C p (.node p s r votes support ats v)
    (chainStateOf C p) hpB (fun a h => on_chain_node_of_parent a p s r votes support ats v h)
    (fun a h => on_chain_node_of_mem a p s r votes support ats v h)
    (chainCertified_chainStateOf C p)
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ChainState V,
      σ₁ = process_attestations (chainStateOf C p) (.node p s r votes support ats v) ats :=
    ⟨_, rfl⟩
  obtain ⟨tp, pr, fp, heq, -⟩ :=
    process_attestations_eq (chainStateOf C p) (.node p s r votes support ats v) ats
  have hw : ParticipationWitnessed
      (fun a => on_chain a (.node p s r votes support ats v) = true) σ₁ := by
    rw [hσ₁]; exact hc.witnessed
  have hh : σ₁.h = (chainStateOf C p).h := by rw [hσ₁, heq]
  have hT : σ₁.T_h = (chainStateOf C p).T_h := by rw [hσ₁, heq]
  have hs : σ₁.s = s := by rw [hσ₁, heq]; rfl
  have hB : chainStateOf C (.node p s r votes support ats v) = process_height_events C σ₁ := by
    rw [hσ₁]; rfl
  obtain ⟨F', h_F', -, hb⟩ := process_height_events_branches C σ₁
  rw [← hh, ← hT]
  rcases hb with ⟨hq, -⟩ | ⟨-, hq, hδ, -⟩ | ⟨-, -, hR⟩
  · have hJ : JustificationCertOn (.node p s r votes support ats v) σ₁.h σ₁.T_h := by
      refine ⟨σ₁.target_participation, hq, fun v hv => ?_⟩
      obtain ⟨a, h1, h2, h3, h4, h5⟩ := hw.target v hv
      exact ⟨a, h2, h3, h4, h5, h1⟩
    refine ⟨?_, Or.inl hJ⟩
    obtain ⟨A, hA, hAv⟩ := hJ
    exact ⟨A, hA, fun v hv => by
      obtain ⟨a, h1, h2, h3, -, h5⟩ := hAv v hv
      exact ⟨a, h1, h2, h3, h5⟩⟩
  · refine ⟨⟨σ₁.progress, hq, fun v hv => ?_⟩, Or.inr ?_⟩
    · obtain ⟨a, h1, h2, h3, h4⟩ := hw.progress v hv
      exact ⟨a, h2, h3, h4, h1⟩
    · rw [← hs]; exact hδ
  · exfalso
    rw [hB, hR] at hadv
    change σ₁.h = (chainStateOf C p).h + 1 at hadv
    omega_nat

/-- **Lemma 67 (b), the first advance past a height, with its branch.** The proof; the audited
statement is in `Statements/Routines/CertificateStatements.lean`.

The variables:
- `C`: the parameters; `B`: the block; `h`: the height. -/
theorem lem67b_first_advance_cases (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (chainStateOf C Y.parent).h = h ∧ (chainStateOf C Y).h = h + 1 ∧
      (chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn Y h (chainStateOf C Y.parent).T_h ∧
      (JustificationCertOn Y h (chainStateOf C Y.parent).T_h ∨
        (chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot) := by
  induction B with
  | genesis =>
      exfalso
      have h0 : (chainStateOf C (Block.genesis : Block V)).h = 1 := rfl
      rw [h0] at hlt
      omega_nat
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have hpB : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      by_cases hp : h < (chainStateOf C p).h
      · obtain ⟨Y, hY, hY1, hY2, hY3, hY4, hY5, hY6⟩ := ih hp
        exact ⟨Y, ancestorEq_trans hY hpB, hY1, hY2, hY3, hY4, hY5, hY6⟩
      · have h2 := chainStateOf_height C _ hne
        change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
        have hadv : (chainStateOf C (.node p s r votes support ats v)).h =
            (chainStateOf C p).h + 1 := by
          rcases h2 with h2 | h2 <;> omega_nat
        have hhp : (chainStateOf C p).h = h := by omega_nat
        obtain ⟨hP, hJ⟩ := progressCertOn_of_advance_cases C p s r votes support ats v hadv
        refine ⟨.node p s r votes support ats v, ancestorEq_refl _, hne, hhp, ?_, ?_, ?_, ?_⟩
        · rw [hadv, hhp]
        · exact ancestorEq_trans (chainStateOf_T_h_spec C p).1 hpB
        · change ProgressCertOn _ h (chainStateOf C p).T_h
          rw [← hhp]
          exact hP
        · change JustificationCertOn _ h (chainStateOf C p).T_h ∨
            (chainStateOf C p).T_h.slot + C.δt ≤ s
          rw [← hhp]
          exact hJ

end GoldilocksCorrectness.Proofs.Routines
