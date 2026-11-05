module
public import GoldilocksCorrectness.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Proofs.Routines.Wiring
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# What the tick's duties sign and propose

`attest_record_grows`, `attest_record_rel`, `tick_record_grows`, `tick_record_rel`,
`propose_block_Λ_rel`: what the attestation duty and the tick add to the signing record;
`propose_block_runs`, `block_admissible_of_proposalBlock`, `tick_proposal_mem_T`: the block the
proposal duty builds, that it passes `block_admissible`, and that a block a tick sends is in the
block tree the tick leaves.

They read the node routines and node states alone: no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every answer of the proposal is `on_block` of the node state on the block it built, which is
the one object it sends.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the proposal sends the block it built, and then receives it. -/
theorem propose_block_runs (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    DREBRuns (fun n' l => ∃ B : Block V, l = [NamedObject.block B] ∧
        ProposalBlock C X n.S n.A (fg_to_ac n.S) n.t n.v B ∧ n' = on_block C P X n B)
      (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBRuns.liftM_bind (fun pr hpr => ?_)
  refine DREBRuns.bind (DREBRuns.broadcast _) (fun _ l₁ hl₁ => DREBRuns.pure ?_)
  rw [hl₁, List.append_nil]
  exact ⟨_, rfl, ⟨pr, hpr, rfl⟩, rfl⟩

/-- The block the proposal builds on a node state at the start of a slot passes `block_admissible`
on that node state, when its root is new to the node, every attestation of the node's pool of
attestations is well formed (the block's attestations are some of them, `proposal_attestations`),
its parent is held, the finalized block is an ancestor of it or it, its parent's slot is earlier than
the slot of the clock, the node's validator is the proposer of that slot, and every vote of the
pool of the previous slot has that slot and a validator of that slot's committee.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block.

Read aloud: the proposer accepts its own block, under the conditions the construction does not
supply. -/
theorem block_admissible_of_proposalBlock (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V)
    -- `B` is the block the proposal builds on `n`
    (hPB : ProposalBlock C X n.S n.A (fg_to_ac n.S) n.t n.v B)
    -- the node's validator is the proposer of the slot of its clock
    (hv : n.v = P.proposer (C.slot n.t))
    -- every vote of the pool of the previous slot has that slot and a committee member
    (hKeyed : ∀ vote ∈ n.A.gf_votes (C.slot n.t - 1),
      vote.slot = C.slot n.t - 1 ∧ vote.val_index ∈ P.committee (C.slot n.t - 1))
    -- the conditions the construction does not supply
    (hRootNew : ∀ B' ∈ n.S.T, B'.root ≠ B.root)
    (hPool : ∀ a ∈ n.S.attestations, attestation_well_formed a = true)
    (hParentHeld : B.parent ∈ n.S.T) (hF : n.S.F.AncestorEq B)
    (hps : B.parent.slot < C.slot n.t) :
    block_admissible C P X n B = true := by
  obtain ⟨pr, hpr, rfl⟩ := hPB
  -- the attestations: those of the pool `proposal_attestations` keeps, so well formed
  have hAtts : ∀ a ∈ proposal_attestations n.S pr.H, attestation_well_formed a = true :=
    fun a ha => hPool a (List.mem_filter.1 ha).1
  obtain ⟨hvotes, hsupport, -⟩ := ac_proposal_facts C n.A (fg_to_ac n.S) n.t pr hpr
  -- the payload: the votes are the pool's list of the previous slot
  have hpay : ac_valid_payload P (Block.node pr.H (C.slot n.t)
      (X.digest pr.H.root (C.slot n.t) (proposal_attestations n.S pr.H) pr.votes
        pr.support_votes) pr.votes pr.support_votes (proposal_attestations n.S pr.H) n.v) =
      true := by
    simp only [ac_valid_payload, decide_eq_true_eq]
    refine ⟨fun vote hvote => ?_, fun vote hvote => ((hsupport vote).1 hvote).1,
      fun vote hvote => ?_⟩
    · rw [hvotes] at hvote
      exact (hKeyed vote hvote).1
    · rw [hvotes] at hvote
      exact (hKeyed vote hvote).2
  refine GoldilocksCorrectness.Proofs.Routines.block_admissible_of C P X n _ ?_ (le_refl _)
    hRootNew hParentHeld hF ?_ hps ?_
  · -- well formed: the attestations, the payload, the digest of the content
    simp only [block_well_formed, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hAtts, hpay⟩, rfl⟩
  · -- the proposer: the node's validator, the proposer of the slot
    show some n.v = some (P.proposer (C.slot n.t))
    rw [hv]
  · -- the attestations: `proposal_attestations` keeps only those valid against `S.σ[H]`
    intro a ha
    have ha' := (List.mem_filter.1 ha).2
    simp only [Bool.and_eq_true] at ha'
    exact ha'.1

/-- A block a tick sends is in the tree the tick leaves, when its root is new to the node, every
attestation of the node's pool of attestations is well formed, the node holds its parent, the node's finalized block is an ancestor
of it or it, its parent's slot is earlier than the slot of `t`, and every vote of the node's pool
of the slot before the slot of `t` has that slot and a validator of that slot's committee.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `B`: the block sent.

Read aloud: a proposer whose tick sends a block holds that block after the tick, under the
conditions the construction does not supply. -/
theorem tick_proposal_mem_T (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (B : Block V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hBlock : NamedObject.block B ∈ sent)
    -- every vote of the pool of the previous slot has that slot and a committee member
    (hKeyed : ∀ vote ∈ n.A.gf_votes (C.slot t - 1),
      vote.slot = C.slot t - 1 ∧ vote.val_index ∈ P.committee (C.slot t - 1))
    -- the conditions the construction does not supply
    (hRootNew : ∀ B' ∈ n.S.T, B'.root ≠ B.root)
    (hPool : ∀ a ∈ n.S.attestations, attestation_well_formed a = true)
    (hParentHeld : B.parent ∈ n.S.T) (hF : n.S.F.AncestorEq B)
    (hps : B.parent.slot < C.slot t) :
    B ∈ n'.S.T := by
  obtain ⟨hS, hA, hv, -⟩ := record_awake_frame n t
  -- the arithmetic of the slot's start, over `Int`
  have hstart : ∀ a d : Int, 0 < d → a ≠ a + d ∧ a ≠ a + 2 * d := by
    intro a d hd
    omega
  -- the relation the tick satisfies, with the conditions on the block in it
  have key : DREBRuns (fun n' l => ∀ B : Block V, NamedObject.block B ∈ l →
      (∀ B' ∈ n.S.T, B'.root ≠ B.root) →
      B.parent ∈ n.S.T → n.S.F.AncestorEq B → B.parent.slot < C.slot t → B ∈ n'.S.T)
      (tick C P X n t) := by
    simp only [tick]
    -- step 1: the tick of the available chain sends no block, and at the start of a slot only
    -- deletes the expired lock entries
    refine DREBRuns.bind (DREBRuns.of_post_emits (ac_on_tick_expire C P _ _ t _ _ _)
      (ac_on_tick_sends C P _ _ t _ _ _)) (fun A₁ l₁ ⟨hA₁, hl₁⟩ => ?_)
    have hnb₁ : NoBlock l₁ := fun B' hB' => by
      obtain ⟨⟨_, heq⟩, -⟩ := hl₁.2 _ hB'
      cases heq
    refine DREBRuns.ite (fun hc => ?_) (fun _ => ?_)
    · -- step 2: the proposal's `if` was taken
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨-, ht⟩, hprop⟩, -⟩ := hc
      have hA₁' : A₁ = expireLocks n.A t := by
        rw [← hA]
        refine hA₁ ?_ ?_
        · exact fun h => (hstart (C.t_ (C.slot t)) C.Δ C.Δ_pos).1 (ht.symm.trans h)
        · exact fun h => (hstart (C.t_ (C.slot t)) C.Δ C.Δ_pos).2 (ht.symm.trans h)
      refine DREBRuns.bind (propose_block_runs C P X _) (fun n₅ l₄ ⟨B₀, hl₄, hPB, hn₅⟩ => ?_)
      -- step 3: the block the proposal built is in the tree `on_block` leaves
      have hB₀ : (∀ B' ∈ n.S.T, B'.root ≠ B₀.root) →
          B₀.parent ∈ n.S.T → n.S.F.AncestorEq B₀ → B₀.parent.slot < C.slot t →
          B₀ ∈ n₅.S.T := by
        intro h1 h3 h4 h5
        rw [hn₅]
        refine GoldilocksCorrectness.Proofs.Routines.mem_T_receive_block C P X _ B₀
          (Or.inr ?_)
        refine block_admissible_of_proposalBlock C P X _ B₀ hPB hprop ?_ ?_ ?_ ?_ ?_ h5
        · intro vote hvote
          rw [hA₁'] at hvote
          exact hKeyed vote hvote
        · rw [hS]; exact h1
        · rw [hS]; exact hPool
        · rw [hS]; exact h3
        · rw [hS]; exact h4
      -- step 4: the attestation duty keeps the tree, and sends no block
      refine DREBRuns.ite (fun _ => ?_) (fun _ => ?_)
      · refine DREBRuns.bind (DREBRuns.of_post_emits (attest_T C n₅) (attest_sends C n₅))
          (fun n₆ l₆ ⟨hT₆, hl₆⟩ => DREBRuns.pure ?_)
        intro B hB h1 h3 h4 h5
        rw [hT₆]
        rcases List.mem_append.1 hB with hB | hB
        · exact absurd hB (hnb₁ B)
        rw [hl₄, List.append_nil] at hB
        rcases List.mem_append.1 hB with hB | hB
        · rw [List.mem_singleton] at hB
          injection hB with hB
          subst hB
          exact hB₀ h1 h3 h4 h5
        · rcases hl₆ with rfl | ⟨a, rfl⟩
          · exact absurd hB List.not_mem_nil
          · simp at hB
      · refine DREBRuns.pure ?_
        intro B hB h1 h3 h4 h5
        rcases List.mem_append.1 hB with hB | hB
        · exact absurd hB (hnb₁ B)
        rw [hl₄, List.append_nil, List.mem_singleton] at hB
        injection hB with hB
        subst hB
        exact hB₀ h1 h3 h4 h5
    · -- the proposal's `if` was not taken: no block is sent
      refine DREBRuns.ite (fun _ => ?_) (fun _ => ?_)
      · refine DREBRuns.bind (DREBRuns.of_post_emits (DREBPost.true _) (attest_sends C _))
          (fun n₆ l₆ ⟨_, hl₆⟩ => DREBRuns.pure ?_)
        intro B hB
        rcases List.mem_append.1 hB with hB | hB
        · exact absurd hB (hnb₁ B)
        rw [List.append_nil] at hB
        rcases hl₆ with rfl | ⟨a, rfl⟩
        · exact absurd hB List.not_mem_nil
        · simp at hB
      · refine DREBRuns.pure ?_
        intro B hB
        rw [List.append_nil] at hB
        exact absurd hB (hnb₁ B)
  obtain ⟨l, hl, hR⟩ := key [] n' sent (DREB.run_eq_of_mem_outcomes hRun)
  rw [List.nil_append] at hl
  subst hl
  exact hR B hBlock hRootNew hParentHeld hF hps

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the attestation duty writes into the record: only the content of the attestation it
sends.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_record_rel (C : Config) (n : NodeState V) :
    DREBRel (fun n' l => RecordFromSent n n' l) (attest C n) := by
  simp only [attest]
  refine DREBRel.bind (DREBRel.liftM _) (fun fi l₁ ⟨hfi, hl₁⟩ => ?_)
  subst hl₁
  obtain ⟨src?, head⟩ := fi
  cases src? with
  | none =>
      simp only [List.nil_append, ne_eq, not_true_eq_false, dite_false]
      exact DREBRel.pure (RecordFromSent.of_Λ rfl)
  | some source =>
      have hrec := create_attestation_record n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ head).h_j (n.S.σ head).J.root (n.S.σ head).h_F
      simp only [List.nil_append, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
        Option.value, Option.get_some]
      split
      · rename_i ha
        obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.mp ha
        rw [get_eq_of_eq_some ha₀]
        refine DREBRel.bind (DREBRel.broadcast _) (fun u l₁ hl₁ => ?_)
        subst hl₁
        refine DREBRel.pure (fun b hb => ?_)
        rw [on_attestation_Λ] at hb
        have ha₀' : (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
            (n.S.σ head).h_j (n.S.σ head).J.root (n.S.σ head).h_F).2 = some a₀ := ha₀
        obtain ⟨hv, hsent⟩ := hrec.2 a₀ ha₀'
        rcases hsent b hb with hb' | hb'
        · exact Or.inl hb'
        · exact Or.inr ⟨a₀, by simp, hb'.symm, hv⟩
      · rename_i ha
        simp only [Decidable.not_not] at ha
        refine DREBRel.pure (RecordFromSent.of_Λ ?_)
        exact hrec.1 ha

/-- The proposal keeps the record: it writes the FG and AC states only.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_Λ_rel (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    DREBRel (fun n' _ => n'.Λ = n.Λ) (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBRel.bind (DREBRel.liftM _) (fun p l₁ _ => ?_)
  obtain ⟨H, votes, support⟩ := p
  refine DREBRel.bind (DREBRel.broadcast _) (fun u l₂ _ => ?_)
  refine DREBRel.pure ?_
  rw [on_block_eq]
  split <;> rfl

/-- What a tick writes into the record: only the contents of the attestations it sends, each of
the tick's validator.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_record_rel (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBRel (fun n' l => RecordFromSent n n' l) (tick C P X n t) := by
  obtain ⟨-, -, hv, -⟩ := record_awake_frame n t
  have hΛ := record_awake_Λ n t
  simp only [tick]
  refine DREBRel.bind (DREBRel.of_emits (ac_on_tick_sends C P _ _ t _ _ _))
    (fun A₁ l₁ _ => ?_)
  refine DREBRel.ite (fun hc₁ => ?_) (fun _ => ?_)
  · -- the proposal ran, at the start of the slot: the attestation duty does not run
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁
    have hstart : t = C.t_ (C.slot t) := hc₁.1.1.2
    refine DREBRel.bind (propose_block_Λ_rel C P X _) ?_
    intro n₄ l₂ hl₂
    refine DREBRel.ite (fun hc₂ => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      exact absurd (hstart.symm.trans hc₂.1) (slotStart_ne_actionTime C _)
    · refine DREBRel.pure (RecordFromSent.of_Λ ?_)
      rw [hl₂]
      exact hΛ
  · refine DREBRel.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBRel.bind (attest_record_rel C _) (fun n₅ l₂ hl₂ => ?_)
      refine DREBRel.pure (fun b hb => ?_)
      rcases hl₂ b hb with hb' | ⟨a, ha, hab, hav⟩
      · left
        rw [← hΛ]
        exact hb'
      · right
        dsimp only at hav
        rw [hv] at hav
        exact ⟨a, (by simp [ha]), hab, hav⟩
    · exact DREBRel.pure (RecordFromSent.of_Λ hΛ)

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every answer of the attestation duty holds every content of the record it starts from.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_record_grows (C : Config) (n : NodeState V) :
    DREBRel (fun n' _ => n.Λ.sent ⊆ n'.Λ.sent) (attest C n) := by
  simp only [attest]
  refine DREBRel.bind (DREBRel.liftM _) (fun fi l₁ _ => ?_)
  obtain ⟨src?, head⟩ := fi
  cases src? with
  | none =>
      simp only [ne_eq, not_true_eq_false, dite_false]
      exact DREBRel.pure (Finset.Subset.refl _)
  | some source =>
      have hrec := create_attestation_sent_subset n.Λ n.v (n.S.σ source).h
        (n.S.σ source).T_h.root (n.S.σ head).h_j (n.S.σ head).J.root (n.S.σ head).h_F
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some]
      split
      · refine DREBRel.bind (DREBRel.broadcast _) (fun u l₂ _ => ?_)
        refine DREBRel.pure ?_
        rw [on_attestation_Λ]
        exact hrec
      · exact DREBRel.pure hrec

/-- Every answer of the node's tick at the time `t` holds every content of the record it starts
from: the proposal keeps the record and the attestation duty only adds to it.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_record_grows (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBRel (fun n' _ => n.Λ.sent ⊆ n'.Λ.sent) (tick C P X n t) := by
  have hΛ := record_awake_Λ n t
  have hatt : ∀ n₀ : NodeState V, n.Λ.sent ⊆ n₀.Λ.sent →
      DREBRel (fun n' (_ : List (NamedObject V)) => n.Λ.sent ⊆ n'.Λ.sent) (attest C n₀) :=
    fun n₀ h => (attest_record_grows C n₀).mono (fun _ _ h' => h.trans h')
  simp only [tick]
  refine DREBRel.bind (DREBRel.of_emits (ac_on_tick_sends C P _ _ t _ _ _))
    (fun A₁ l₁ _ => ?_)
  have h₀ : n.Λ.sent ⊆
      ({ { record_awake n t with t := t } with A := A₁ } : NodeState V).Λ.sent := by
    show n.Λ.sent ⊆ (record_awake n t).Λ.sent
    rw [hΛ]
  refine DREBRel.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBRel.bind (propose_block_Λ_rel C P X _) (fun n₄ l₂ hl₂ => ?_)
    have h₄ : n.Λ.sent ⊆ n₄.Λ.sent := by
      rw [hl₂]
      exact h₀
    refine DREBRel.ite (fun _ => ?_) (fun _ => DREBRel.pure h₄)
    exact DREBRel.bind (hatt n₄ h₄) (fun n₅ l₃ h₅ => DREBRel.pure h₅)
  · refine DREBRel.ite (fun _ => ?_) (fun _ => DREBRel.pure h₀)
    exact DREBRel.bind (hatt _ h₀) (fun n₅ l₃ h₅ => DREBRel.pure h₅)

end

end

end GoldilocksCorrectness.Proofs.Routines
