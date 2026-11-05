module
public import GoldilocksCorrectness.Record.TickFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick
public import GoldilocksCorrectness.Proofs.Routines.NodeSends
public import GoldilocksCorrectness.Proofs.Routines.NodeReach
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
public import GoldilocksCorrectness.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Routines.HeldAttestations
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's tick facts, part 1

`tickFacts1_goldilocks`: the spec's model satisfies `TickFacts1`. At `Model.goldilocks` the tick's
outcomes are those of the spec's duty `Goldilocks.tick`, and a landed theorem about every answer of
the duty (`DREBPost`, `DREBSpec`, `DREBEmits`, `DREBRel`) gives the field at every `.ok` outcome
(`….of_outcome`). The fields that take the model's node invariant pass its clause
`ChainStatesComputed` to the landed theorem. The wake test on the tick's answer is the landed one on
the state the tick's first step leaves (`tick_awakeSince`): the test reads `awakeSince` alone. The
validator, which the landed theorems keep only under the node invariant, is kept by every answer of
the proposal, the attestation duty and the tick, proved here as `tick_nodeInv` is, with the
postcondition "the validator is `n`'s".
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block Attestation NamedObject NodeState
  Time)
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBSpec DREBEmits DREBRel)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- The wake test reads `awakeSince` alone: two node states with the same `awakeSince` pass it for
the same times.

The variables:
- `n₁`, `n₂`: the node states; `h`: they have the same `awakeSince`; `t₀`: the time tested.

Read aloud: the wake test of a node state depends on its wake time only. -/
theorem awake_since_congr {n₁ n₂ : NodeState V} (h : n₁.awakeSince = n₂.awakeSince) (t₀ : Time) :
    n₁.awake_since t₀ = n₂.awake_since t₀ := by
  simp only [Goldilocks.NodeState.awake_since, h]

section

variable [RootOrder]

/-- Receiving a block keeps the validator.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block.

Read aloud: receiving a block does not change the validator. -/
theorem on_block_validator (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) : (Goldilocks.on_block C P X n B).v = n.v := by
  rw [GoldilocksCorrectness.Proofs.Routines.on_block_eq]
  split <;> rfl

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the validator.

The variables:
- `n`: the node state; `a`: the attestation.

Read aloud: receiving an attestation does not change the validator. -/
theorem on_attestation_validator (n : NodeState V) (a : Attestation V) :
    (Goldilocks.on_attestation n a).v = n.v := by
  simp only [Goldilocks.on_attestation, Id.run]
  split <;> rfl

/-- Every answer of the proposal keeps the validator: it ends by receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the proposal does not change the validator. -/
theorem propose_block_validator (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) :
    DREBPost (Goldilocks.propose_block C P X n) (fun n' => n'.v = n.v) := by
  simp only [Goldilocks.propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_validator C P X n _)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the attestation duty keeps the validator: it writes the anti-slashing record,
and may receive its own attestation.

The variables:
- `C`: the parameters; `n`: the node state.

Read aloud: the attestation duty does not change the validator. -/
theorem attest_validator (C : Config) (n : NodeState V) :
    DREBPost (Goldilocks.attest C n) (fun n' => n'.v = n.v) := by
  simp only [Goldilocks.attest]
  refine DREBPost.bind_any (fun fi => ?_)
  obtain ⟨src?, head⟩ := fi
  repeat' first
    | exact DREBPost.pure rfl
    | exact DREBPost.pure (on_attestation_validator _ _)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick keeps the validator.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: a tick does not change the validator. -/
theorem tick_validator (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) : DREBPost (Goldilocks.tick C P X n t) (fun n' => n'.v = n.v) := by
  obtain ⟨-, -, hv, -⟩ := GoldilocksCorrectness.Proofs.Routines.record_awake_frame n t
  simp only [Goldilocks.tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : ({ { Goldilocks.record_awake n t with t := t } with A := A' } : NodeState V).v = n.v :=
    hv
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind ((propose_block_validator C P X _).mono (fun _ h => h.trans hq))
      (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind ((attest_validator C _).mono (fun _ h => h.trans h₄))
        (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind ((attest_validator C _).mono (fun _ h => h.trans hq))
        (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

end

/-- The spec's model satisfies the facts about the tick, part 1.

Read aloud: a Goldilocks tick sets the clock, records a wake, expires the locks, grows what the
node holds, changes a confirmation only at an awake node's support cutoff, and sends only its own
duties' objects. -/
theorem tickFacts1_goldilocks : TickFacts1 (Model.goldilocks (V := V)) where
  tick_clock_validator_awakeSince C P X n t n' sent hm := by
    refine ⟨DREBPost.of_outcome (tick_validator C P X n t) hm,
      (DREBSpec.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_prov C P X n t) hm).2, ?_⟩
    have h := GoldilocksCorrectness.Proofs.Routines.tick_awakeSince C P X n n' t sent hm
    show NodeState.awakeSince (n' : NodeState V) =
      some (match NodeState.awakeSince (n : NodeState V) with | none => t | some τ => τ)
    rw [h]
    cases hn : NodeState.awakeSince (n : NodeState V) with
    | none => exact GoldilocksCorrectness.Proofs.Routines.record_awake_awakeSince_none hn
    | some τ => exact GoldilocksCorrectness.Proofs.Routines.record_awake_awakeSince_some hn
  tick_lock_entries C P X n t n' sent hm := by
    rcases GoldilocksCorrectness.Proofs.Routines.tick_period_cases C P X n n' t sent hm with
      ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  tick_keeps_confirmation_off_cutoff C P X n t n' sent hm hc := by
    refine ⟨?_, ?_, ?_⟩
    · rcases GoldilocksCorrectness.Proofs.Routines.tick_cases C P X n n' t sent hm with
        ⟨h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h
      · exact absurd h hc
    · rcases GoldilocksCorrectness.Proofs.Routines.tick_period_cases C P X n n' t sent hm with
        ⟨-, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨h, -⟩
      · exact h
      · exact h
      · exact absurd h hc
    · rcases GoldilocksCorrectness.Proofs.Routines.tick_latest_cases C P X n n' t sent hm with
        h | ⟨h, -⟩
      · exact h
      · exact absurd h hc
  tick_confirmation_awake C P X n t n' sent hm := by
    rcases GoldilocksCorrectness.Proofs.Routines.tick_cases C P X n n' t sent hm with
      ⟨hs, -⟩ | ⟨-, -, -, hs, -⟩ | ⟨hc, haw, -⟩
    · rcases GoldilocksCorrectness.Proofs.Routines.tick_latest_cases C P X n n' t sent hm with
        hl | ⟨hc, haw, -⟩
      · exact Or.inl ⟨hs, hl⟩
      · exact Or.inr ⟨hc, haw⟩
    · rcases GoldilocksCorrectness.Proofs.Routines.tick_latest_cases C P X n n' t sent hm with
        hl | ⟨hc, haw, -⟩
      · exact Or.inl ⟨hs, hl⟩
      · exact Or.inr ⟨hc, haw⟩
    · exact Or.inr ⟨hc, haw⟩
  tick_step C P X n t n' sent hm hk := by
    obtain ⟨h1, h2, ⟨h3, h4⟩, h5⟩ :=
      DREBPost.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_step C P X n t hk) hm
    have h5' : NodeState.t (n' : NodeState V) = t := h5
    rw [h5'] at h3 h4
    exact ⟨h1, h2, ⟨h3, h4⟩, h5⟩
  tick_tree_mono C P X n t n' sent hm :=
    (DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_reachFrom C P X Block.genesis n t) hm).1
  tick_pool C P X n t n' sent hm :=
    DREBPost.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_pool C P X n t) hm
  tick_chainsInPool C P X n t n' sent hm h :=
    DREBPost.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_chainsInPool C P X n t h) hm
  tick_prov C P X n t n' sent hm :=
    (DREBSpec.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_prov C P X n t) hm).1
  tick_prov_attestations C P X n t n' sent hm :=
    DREBSpec.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_prov_attestations C P X n t) hm
  tick_finalizedFrom C P X n t n' sent hm h :=
    DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_finalizedFrom C P X n t h.1.2.2.2.2.2.1) hm
  tick_justifiedFrom C P X n t n' sent hm h :=
    DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_justifiedFrom C P X n t h.1.2.2.2.2.2.1) hm
  tick_cachesFrom C P X H OnChain n t n' sent hm h :=
    DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_cachesFrom C P X H OnChain n t h.1.2.2.2.2.2.1) hm
  tick_sends C P X n t n' sent hm := GoldilocksCorrectness.Proofs.Routines.tick_sends C P X n t hm
  tick_emits_vote C P X n t n' sent hm hv haw hc := by
    have hA := GoldilocksCorrectness.Proofs.Routines.tick_awakeSince C P X n n' t sent hm
    exact DREBEmits.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_emits_vote C P X n t)
      hm hv ((awake_since_congr hA.symm _).trans haw) hc
  tick_emits_proposal C P X n t n' sent hm hs hst hp haw := by
    have hA := GoldilocksCorrectness.Proofs.Routines.tick_awakeSince C P X n n' t sent hm
    exact DREBEmits.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_emits_proposal C P X n t)
      hm hs hst hp ((awake_since_congr hA.symm _).trans haw)
  tick_attest_awake C P X n t n' sent hm a ha := by
    have hA := GoldilocksCorrectness.Proofs.Routines.tick_awakeSince C P X n n' t sent hm
    exact (awake_since_congr hA _).trans
      (DREBRel.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_attest_awake C P X n t)
        hm a ha)
  tick_proposal_mem_tree C P X n t n' sent B hm hB hK hR hP hpar hF hps :=
    GoldilocksCorrectness.Proofs.Routines.tick_proposal_mem_T C P X n n' t sent B hm hB hK hR hP
      hpar hF hps
  tick_block_unique C P X n t n' sent B B' hm hB hB' :=
    GoldilocksCorrectness.Proofs.Routines.tick_block_unique C P X n n' t sent B B' hm hB hB'
  tick_record_rel C P X n t n' sent hm :=
    DREBRel.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_record_rel C P X n t) hm
  tick_record_grows C P X n t n' sent hm :=
    DREBRel.of_outcome (GoldilocksCorrectness.Proofs.Routines.tick_record_grows C P X n t) hm

end GoldilocksCorrectness.Record
