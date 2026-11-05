module
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Routines.PoolInv
public import GoldilocksCorrectness.Statements.Routines.NodeCoreDefs
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The clock-free part of the node invariant, kept by every node routine at any clock

`NodeInvCore` (`Statements/Routines/NodeCoreDefs.lean`) is `NodeInv` without its two clock clauses,
`StampsBounded` and `StampOrder`. Every node routine keeps it with no condition on the clock: the
tick and the wake at any time `t`, a delivery as before. The theorems here are the clock-free twins
of the landed `…_nodeInv` theorems (`Node.lean`, `Wiring.lean`) and of the AC pool lemmas
(`ACStore.lean`, `ACInterface.lean`, `ForkChoiceFacts.lean`, `RevokeLocks.lean`, `Confirmation.lean`):
the same proofs with the two stamp cases and the clock condition removed, the pool read through
`PoolInv` (`PoolInv.lean`) in place of `VotesInv` (which adds the stamp bound). The projections
`NodeInv.core`, `NodeInv.clock`, `nodeInv_of_core` and the twins `nodeInvCore_of_frame`,
`on_block_nodeInvCore`, `nodeInvCore_of_record` are in `Node.lean`, where the landed theorems are proved
from them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Receiving a Goldfish vote keeps `NodeInvCore`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `vote`: the vote.

Read aloud: receiving a vote keeps the clock-free part. -/
theorem on_ac_message_nodeInvCore (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (vote : GoldfishVote V) (h : NodeInvCore C P X n) :
    NodeInvCore C P X (on_ac_message C P n vote) ∧ (on_ac_message C P n vote).v = n.v ∧
      (on_ac_message C P n vote).t = n.t := by
  have he : on_ac_message C P n vote = { n with A := on_goldfish_vote C P n.A n.t vote } := rfl
  rw [he]
  exact ⟨nodeInvCore_of_frame h rfl rfl rfl rfl rfl rfl rfl
    (on_goldfish_vote_timestamp_block C P n.A n.t vote)
    (on_goldfish_vote_poolInv C P n.A n.t vote ⟨h.1, h.2.1⟩) h.2.2.2.2.2.2.2.2, rfl, rfl⟩

/-- Receiving an attestation keeps `NodeInvCore`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `a`: the attestation.

Read aloud: receiving an attestation keeps the clock-free part. -/
theorem on_attestation_nodeInvCore (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (a : Attestation V) (h : NodeInvCore C P X n) :
    NodeInvCore C P X (on_attestation n a) ∧ (on_attestation n a).v = n.v ∧
      (on_attestation n a).t = n.t := by
  simp only [on_attestation, Id.run]
  split
  · exact ⟨h, rfl, rfl⟩
  · rename_i hwf
    have ha : attestation_well_formed a = true := by simpa using hwf
    obtain ⟨h1, h2, h3⟩ := fg_on_attestation_keeps n.S a
    obtain ⟨h4, h5⟩ := fg_on_attestation_caches n.S a
    exact ⟨nodeInvCore_of_frame h h1 h2 h3 h4 h5 (fg_on_attestation_h_j n.S a) rfl rfl
      ⟨h.1, h.2.1⟩ (fg_on_attestation_wf n.S a h.2.2.2.2.2.2.2.2 ha), rfl, rfl⟩

/-- Waking at ANY time `t` keeps `NodeInvCore` and the validator and sets the clock to `t`.
`wake_nodeInv` without its clock condition.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the wake time.

Read aloud: a wake at any time keeps the clock-free part. -/
theorem wake_nodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (h : NodeInvCore C P X n) :
    NodeInvCore C P X (wake n t) ∧ (wake n t).v = n.v ∧ (wake n t).t = t :=
  ⟨nodeInvCore_of_frame h (n' := wake n t) rfl rfl rfl rfl rfl rfl rfl rfl ⟨h.1, h.2.1⟩
    h.2.2.2.2.2.2.2.2, rfl, rfl⟩

section

variable [RootOrder]

/-- Every answer of the proposal keeps `NodeInvCore`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the proposal keeps the clock-free part. -/
theorem propose_block_nodeInvCore (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (h : NodeInvCore C P X n) :
    DREBPost (propose_block C P X n)
      (fun n' => NodeInvCore C P X n' ∧ n'.v = n.v ∧ n'.t = n.t) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_nodeInvCore C P X n _ h)
    | refine DREBPost.bind_any (fun _ => ?_)

end

/-- The record `fg_attest` returns keeps `NodeInvCore`, when the head is a block of the tree of which
the finalized block is an ancestor, or which is the finalized block. `fg_attest_nodeInv` for the
clock-free part.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `source`, `head`: the blocks
  the attestation is built from.

Read aloud: the attestation's record keeps the clock-free part. -/
theorem fg_attest_nodeInvCore {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInvCore C P X n) (source head : Block V)
    (hhead : head ∈ n.S.T) (hFh : n.S.F.AncestorEq head) :
    NodeInvCore C P X { n with Λ := (fg_attest n.S n.Λ n.v source head).1 } := by
  have hJCB : JustificationCacheBounds n.S := h.2.2.2.2.2.2.2.1.2.2.1
  have hLBJ : LockBelowJustified n := h.2.2.2.2.2.2.2.1.2.2.2.2.2.1
  have hRC : RecordConsistent n.Λ := h.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  refine nodeInvCore_of_record h _ (fun hh T hl => ?_) ?_
  · rw [fg_attest_eq] at hl
    rcases create_attestation_lock _ _ _ _ _ _ _ hh T hl with hl' | hh'
    · exact hLBJ hh T hl'
    · show hh ≤ n.S.h_j
      rw [hh']
      exact hJCB head hhead hFh
  · rw [fg_attest_eq]
    exact (GoldilocksCorrectness.Proofs.Routines.lem72_create_attestation_consistent _ _ _ _ _ _ _
      hRC).1

section

variable [RootOrder]

/-- Every answer of the attestation duty keeps `NodeInvCore`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the attestation duty keeps the clock-free part. -/
theorem attest_nodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (h : NodeInvCore C P X n) :
    DREBPost (attest C n) (fun n' => NodeInvCore C P X n' ∧ n'.v = n.v ∧ n'.t = n.t) := by
  have hhead := ac_to_fg_head_mem C n.A n.S n.t h.2.2.2.1 h.2.2.2.2.2.2.2.1.2.2.2.2.1
    h.2.2.2.2.2.2.2.1.2.1.1
  simp only [attest]
  refine DREBPost.bind (DREBPost.liftM hhead) (fun fi hfi => ?_)
  have hrec : ∀ source : Block V,
      NodeInvCore C P X { n with Λ := (fg_attest n.S n.Λ n.v source fi.head).1 } :=
    fun source => fg_attest_nodeInvCore h source fi.head hfi.1 hfi.2
  obtain ⟨src?, head⟩ := fi
  repeat' first
    | exact DREBPost.pure ⟨h, rfl, rfl⟩
    | exact DREBPost.pure ⟨hrec _, rfl, rfl⟩
    | exact DREBPost.pure (on_attestation_nodeInvCore C P X _ _ (hrec _))
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The proposal keeps "`NodeInvCore`, the validator `v` and the clock `t`".

The variables:
- `n`: the node state.

Read aloud: the proposal keeps the clock-free part, the validator and the clock. -/
theorem propose_block_fromCore {C : Config} {P : Provisional V} {X : External V} {v : V} {t : Time}
    (n : NodeState V) (h : NodeInvCore C P X n ∧ n.v = v ∧ n.t = t) :
    DREBPost (propose_block C P X n) (fun n' => NodeInvCore C P X n' ∧ n'.v = v ∧ n'.t = t) :=
  (propose_block_nodeInvCore C P X n h.1).mono
    (fun _ h' => ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩)

/-- The attestation duty keeps "`NodeInvCore`, the validator `v` and the clock `t`".

The variables:
- `n`: the node state.

Read aloud: the attestation duty keeps the clock-free part, the validator and the clock. -/
theorem attest_fromCore {C : Config} {P : Provisional V} {X : External V} {v : V} {t : Time}
    (n : NodeState V) (h : NodeInvCore C P X n ∧ n.v = v ∧ n.t = t) :
    DREBPost (attest C n) (fun n' => NodeInvCore C P X n' ∧ n'.v = v ∧ n'.t = t) :=
  (attest_nodeInvCore C P X n h.1).mono
    (fun _ h' => ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩)

/-- Every answer of the node's tick at ANY time `t` satisfies `NodeInvCore`, keeps the validator, and
has the clock `t`. `tick_nodeInv` without its clock condition.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: a tick at any time keeps the clock-free part and the validator, and sets the clock. -/
theorem tick_nodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (h : NodeInvCore C P X n) :
    DREBPost (tick C P X n t) (fun n' => NodeInvCore C P X n' ∧ n'.v = n.v ∧ n'.t = t) := by
  obtain ⟨hS, hA, hv, -⟩ := record_awake_frame n t
  have hV : PoolInv P (record_awake n t).A := by
    rw [hA]
    exact ⟨h.1, h.2.1⟩
  have h2 : NodeInvCore C P X { record_awake n t with t := t } :=
    nodeInvCore_of_frame h (n' := { record_awake n t with t := t }) (by show _ = _; rw [hS])
      (by show _ = _; rw [hS]) (by show _ = _; rw [hS]) (by show _ = _; rw [hS])
      (by show _ = _; rw [hS]) (by show _ = _; rw [hS]) (record_awake_keeps_record n t)
      (by show _ = _; rw [hA]) hV
      (by show PoolAttestationsWellFormed (record_awake n t).S; rw [hS]
          exact h.2.2.2.2.2.2.2.2)
  simp only [tick]
  refine DREBPost.bind (ac_on_tick_poolInv C P _ _ t _ _ _ hV) (fun A' hA' => ?_)
  have hq : NodeInvCore C P X { { record_awake n t with t := t } with A := A' } ∧
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).v = n.v ∧
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).t = t :=
    ⟨nodeInvCore_of_frame h2 rfl rfl rfl rfl rfl rfl rfl hA'.2 hA'.1 h2.2.2.2.2.2.2.2.2, hv, rfl⟩
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (propose_block_fromCore _ hq) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_fromCore _ h₄) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_fromCore _ hq) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

/-- Receiving an object keeps `NodeInvCore`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object.

Read aloud: a delivery keeps the clock-free part. -/
theorem receive_nodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) (h : NodeInvCore C P X n) :
    NodeInvCore C P X (Goldilocks.Sts.receive C P X n o) ∧
      (Goldilocks.Sts.receive C P X n o).v = n.v ∧ (Goldilocks.Sts.receive C P X n o).t = n.t := by
  cases o with
  | block B => exact on_block_nodeInvCore C P X n B h
  | gfVote vote => exact on_ac_message_nodeInvCore C P X n vote h
  | attest a => exact on_attestation_nodeInvCore C P X n a h

end

end

end GoldilocksCorrectness.Proofs.Routines
