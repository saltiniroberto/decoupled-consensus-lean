module
public import GoldilocksCorrectness.Proofs.Routines.Wiring
import all Goldilocks.FG.State
import all Goldilocks.Node

@[expose] public section

/-!
# What a node routine adds to the attestations a node holds

The attestations a node state `n` holds are the pool `n.S.attestations`. This page proves that a
node routine adds to the pool only attestations it was handed or sent, alone or inside a block:

- `fg_on_attestation_new`, `fg_on_attestations_new`, `fg_on_block_new_attestations`: the FG
  handlers add only the attestation received, or the attestations of the block accepted;
- `on_attestation_new_attestations`, `on_block_new_attestations`: the same for the node handlers;
- `AttestationsNewIn n n' l`, the relation "every attestation `n'` holds and `n` does not is an
  attestation of `l`, or an attestation of a block of `l`", with `of_same` and `trans`;
- `propose_block_attestations_new`, `attest_attestations_new`, `tick_prov_attestations`: every
  answer of the proposal, of the attestation duty and of the tick adds only what it sent;
- `receive_new_attestations`: the wiring's dispatch of a delivered object adds only the object
  itself, when it is an attestation, or the attestations of the delivered block.

They are the attestation twins of `NewObjectsIn`, `propose_block_prov`, `attest_prov`, `tick_prov`
(`Proofs/Routines/Node.lean`) and `receive_new` (`Proofs/Routines/Wiring.lean`), which cover the
Goldfish votes and the tree.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

/-! ## The FG handlers -/

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving the attestation `a` into the FG state `S` adds to the pool at most `a`.

The variables:
- `S`: the FG state; `a`: the attestation received; `a'`: an attestation of the pool after.

Read aloud: an attestation the pool holds after receiving `a` was held before, or is `a`. -/
theorem fg_on_attestation_new (S : FGState V) (a a' : Attestation V)
    -- the pool holds `a'` after `a` is received
    (h : a' ∈ (fg_on_attestation S a).attestations) : a' ∈ S.attestations ∨ a' = a := by
  simp only [fg_on_attestation, Id.run] at h
  split at h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  · exact Or.inl h

omit [Fintype V] in
/-- Receiving the attestations of the list `l` in order into the FG state `S` adds to the pool only
attestations of `l`.

The variables:
- `l`: the attestations received; `S`: the FG state; `a'`: an attestation of the pool after.

Read aloud: an attestation the pool holds after receiving `l` was held before, or is in `l`. -/
theorem fg_on_attestations_new (l : List (Attestation V)) (S : FGState V) (a' : Attestation V)
    -- the pool holds `a'` after the attestations of `l` are received
    (h : a' ∈ (forIn (m := Id) l S
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).attestations) :
    a' ∈ S.attestations ∨ a' ∈ l :=
  forIn_yield_inv l S (fun X a => fg_on_attestation X a)
    (fun X => ∀ a'' : Attestation V, a'' ∈ X.attestations → a'' ∈ S.attestations ∨ a'' ∈ l)
    (fun _ h => Or.inl h)
    (fun X a ha hX a'' h'' => by
      rcases fg_on_attestation_new X a a'' h'' with h | rfl
      · exact hX a'' h
      · exact Or.inr ha) a' h

variable [RootOrder]

/-- Accepting the block `B` into the FG state `S` adds to the pool only attestations `B` includes.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block; `a`: an attestation of the pool after.

Read aloud: an attestation the pool holds after accepting `B` was held before, or is one of
`B`'s attestations. -/
theorem fg_on_block_new_attestations (C : Config) (S : FGState V) (B : Block V)
    (a : Attestation V)
    -- the pool holds `a` after `B` is accepted
    (h : a ∈ (fg_on_block C S B).attestations) : a ∈ S.attestations ∨ a ∈ B.attestations := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef] at h
  rcases fg_on_attestations_new B.attestations _ a h with h | h
  · rw [update_finality_attestations] at h
    exact Or.inl h
  · exact Or.inr h

end

/-! ## The node handlers -/

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving the attestation `a` adds to the node's pool at most `a`.

The variables:
- `n`: the node state; `a`: the attestation received; `a'`: an attestation of the pool after.

Read aloud: an attestation the node holds after receiving `a` was held before, or is `a`. -/
theorem on_attestation_new_attestations (n : NodeState V) (a a' : Attestation V)
    -- the node's pool holds `a'` after `a` is received
    (h : a' ∈ (on_attestation n a).S.attestations) : a' ∈ n.S.attestations ∨ a' = a := by
  simp only [on_attestation, Id.run] at h
  split at h
  · exact Or.inl h
  · exact fg_on_attestation_new n.S a a' h

variable [RootOrder]

/-- Receiving the block `B` adds to the node's pool only attestations `B` includes.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block;
- `a`: an attestation of the pool after.

Read aloud: an attestation the node holds after receiving `B` was held before, or is one of
`B`'s attestations. -/
theorem on_block_new_attestations (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (a : Attestation V)
    -- the node's pool holds `a` after `B` is received
    (h : a ∈ (on_block C P X n B).S.attestations) : a ∈ n.S.attestations ∨ a ∈ B.attestations := by
  rw [on_block_eq] at h
  split at h
  · exact fg_on_block_new_attestations C n.S B a h
  · exact Or.inl h

end

/-! ## The relation, and the duties -/

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `AttestationsNewIn n n' l`: every attestation the pool of `n'` holds and the pool of `n` does
not is an attestation of the list `l`, or an attestation included in a block of `l`.

The variables:
- `n`, `n'`: the two node states; `l`: the list of objects.

Read aloud: what `n'` holds of attestations beyond `n` is in `l`, alone or inside a block. -/
def AttestationsNewIn (n n' : NodeState V) (l : List (NamedObject V)) : Prop :=
  ∀ a ∈ n'.S.attestations, a ∉ n.S.attestations →
    NamedObject.attest a ∈ l ∨ ∃ B : Block V, NamedObject.block B ∈ l ∧ a ∈ B.attestations

omit [DecidableEq V] [Fintype V] in
/-- A node state with the pool of `n` holds no attestation beyond `n`.

The variables:
- `n`, `n'`: the two node states; `l`: the list of objects; `h`: the two pools are equal.

Read aloud: a node state with the same pool adds no attestation. -/
theorem AttestationsNewIn.of_same {n n' : NodeState V} {l : List (NamedObject V)}
    (h : n'.S.attestations = n.S.attestations) : AttestationsNewIn n n' l := by
  intro a ha hn
  rw [h] at ha
  exact absurd ha hn

omit [DecidableEq V] [Fintype V] in
/-- `AttestationsNewIn` composes: what `n₂` holds beyond `n` is beyond `n` in `n₁`, or beyond `n₁`
in `n₂`.

The variables:
- `n`, `n₁`, `n₂`: the node states; `l₁`, `l₂`: the lists of objects.

Read aloud: two steps add only what the first or the second sent. -/
theorem AttestationsNewIn.trans {n n₁ n₂ : NodeState V} {l₁ l₂ : List (NamedObject V)}
    (h : AttestationsNewIn n n₁ l₁) (h' : AttestationsNewIn n₁ n₂ l₂) :
    AttestationsNewIn n n₂ (l₁ ++ l₂) := by
  intro a ha hn
  by_cases ha₁ : a ∈ n₁.S.attestations
  · rcases h a ha₁ hn with h₁ | ⟨B, hB, hB'⟩
    · exact Or.inl (List.mem_append_left _ h₁)
    · exact Or.inr ⟨B, List.mem_append_left _ hB, hB'⟩
  · rcases h' a ha ha₁ with h₁ | ⟨B, hB, hB'⟩
    · exact Or.inl (List.mem_append_right _ h₁)
    · exact Or.inr ⟨B, List.mem_append_right _ hB, hB'⟩

omit [Fintype V] in
/-- Receiving the attestation `a` adds to the pool only `a`, from any node state whose pool is
`n`'s.

The variables:
- `n`: the node state the comparison is with; `n₀`: the node state that receives `a`;
- `a`: the attestation; `h`: the pools of `n₀` and `n` are equal.

Read aloud: receiving `a` adds at most `a`. -/
theorem on_attestation_attestationsNewIn (n n₀ : NodeState V) (a : Attestation V)
    (h : n₀.S.attestations = n.S.attestations) :
    AttestationsNewIn n (on_attestation n₀ a) [NamedObject.attest a] := by
  intro a' ha hn
  rcases on_attestation_new_attestations n₀ a a' ha with h' | rfl
  · rw [h] at h'
    exact absurd h' hn
  · exact Or.inl (List.mem_singleton_self _)

variable [RootOrder]

/-- Every answer of the attestation duty adds to the pool only the attestation it sent.

The variables:
- `C`: the parameters; `n`: the node state.

Read aloud: the attestation duty adds only what it sent. -/
theorem attest_attestations_new (C : Config) (n : NodeState V) :
    DREBSpec (fun n' l => AttestationsNewIn n n' l) (attest C n) := by
  simp only [attest]
  repeat' first
    | exact DREBSpec.pure (AttestationsNewIn.of_same rfl)
    | exact DREBSpec.broadcast_pure _ (on_attestation_attestationsNewIn n _ _ rfl)
    | refine DREBSpec.bind_liftPost (DREPost.true _) (fun _ _ => ?_)
    | refine DREBSpec.dite (fun _ => ?_) (fun _ => ?_)

/-- Every answer of the proposal adds to the pool only attestations of the block it sent.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the proposal adds only the attestations of its own block. -/
theorem propose_block_attestations_new (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) :
    DREBSpec (fun n' l => AttestationsNewIn n n' l) (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBSpec.bind_liftPost (DREPost.true _) (fun p _ => ?_)
  obtain ⟨H, votes, support⟩ := p
  refine DREBSpec.broadcast_pure _ ?_
  intro a ha hn
  rcases on_block_new_attestations C P X n _ a ha with h | h
  · exact absurd h hn
  · exact Or.inr ⟨_, List.mem_singleton_self _, h⟩

/-- Every answer of the node's tick at the time `t` adds to the pool only attestations it sent,
alone or inside a block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: a tick adds to the attestations held only what it sent. -/
theorem tick_prov_attestations (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (t : Time) :
    DREBSpec (fun n' l => AttestationsNewIn n n' l) (tick C P X n t) := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBSpec.bind' (ac_on_tick_prov C P _ _ t _ _ _) (fun A' l₁ _ => ?_)
  have hq : AttestationsNewIn n { { record_awake n t with t := t } with A := A' } l₁ :=
    AttestationsNewIn.of_same (by
      show (record_awake n t).S.attestations = n.S.attestations
      rw [hS])
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBSpec.bind' (propose_block_attestations_new C P X _) (fun n₄ l₂ h₂ => ?_)
    have h₄ : AttestationsNewIn n n₄ (l₁ ++ l₂) := hq.trans h₂
    refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBSpec.bind' (attest_attestations_new C _) (fun n₅ l₃ h₃ => DREBSpec.pure ?_)
      have h₅ := h₄.trans h₃
      simp only [List.append_nil, List.append_assoc] at h₅ ⊢
      exact h₅
    · refine DREBSpec.pure ?_
      simp only [List.append_nil]
      exact h₄
  · refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBSpec.bind' (attest_attestations_new C _) (fun n₅ l₃ h₃ => DREBSpec.pure ?_)
      have h₅ := hq.trans h₃
      simp only [List.append_nil] at h₅ ⊢
      exact h₅
    · refine DREBSpec.pure ?_
      rw [List.append_nil]
      exact hq

/-- The wiring's dispatch of the delivered object `o` adds to the pool only `o`, when `o` is an
attestation, or the attestations of `o`'s block, when `o` is a block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object.

Read aloud: a delivery adds to the attestations held only the delivered attestation, or the
attestations of the delivered block. -/
theorem receive_new_attestations (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (o : NamedObject V) :
    ∀ a ∈ (Goldilocks.Sts.receive C P X n o).S.attestations, a ∉ n.S.attestations →
      o = NamedObject.attest a ∨ ∃ B : Block V, o = NamedObject.block B ∧ a ∈ B.attestations := by
  intro a ha hn
  cases o with
  | block B =>
      rcases on_block_new_attestations C P X n B a ha with h | h
      · exact absurd h hn
      · exact Or.inr ⟨B, rfl, h⟩
  | gfVote vote =>
      change a ∈ (on_ac_message C P n vote).S.attestations at ha
      rw [on_ac_message_eq] at ha
      exact absurd ha hn
  | attest a' =>
      rcases on_attestation_new_attestations n a' a ha with h | rfl
      · exact absurd h hn
      · exact Or.inl rfl

end

end GoldilocksCorrectness.Proofs.Routines
