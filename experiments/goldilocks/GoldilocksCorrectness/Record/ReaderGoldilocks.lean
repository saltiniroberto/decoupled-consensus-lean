module
public import GoldilocksCorrectness.Record.ReaderFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.Lemma35
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.Node
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.AC.State
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.Interface
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's reader facts

`readerFacts_goldilocks`: the spec's model satisfies `ReaderFacts`. At `Model.goldilocks` each
derived reader is the spec's reader applied to the parts of the node state it reads, so most
fields hold by definition (this page sees the spec's bodies). The four fields on the readers of
the anti-slashing record are the library's theorems at the node's record `n.Λ`; the fields written
by cases (`saved_extends_eq`, `ac_confirmed_eq`, `awake_since_eq`, `advance_eq`) and the two `↔`
fields are proved by opening the spec's body, or are the library's theorem of that shape.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Block)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the facts about the readers derived from a node state.

Read aloud: Goldilocks' readers answer what the record says each reader answers. -/
theorem readerFacts_goldilocks : ReaderFacts (Model.goldilocks (V := V)) where
  has_viable_descendant_eq := fun _ _ => rfl
  fg_to_ac_eq := fun _ => rfl
  attestations_on_chain_genesis := rfl
  attestations_on_chain_node := fun _ _ _ _ _ _ _ => rfl
  on_chain_eq := fun _ _ => rfl
  finality_pair_some := fun h => GoldilocksCorrectness.Proofs.Routines.finality_pair_some h
  own_lock_cases := fun n h fp => GoldilocksCorrectness.Proofs.Routines.own_lock_cases n.Λ h fp
  height_pair_vote_cases := fun h => GoldilocksCorrectness.Proofs.Routines.height_pair_vote_cases h
  height_pair_timeout := fun h => GoldilocksCorrectness.Proofs.Routines.height_pair_timeout h
  already_sent_eq := fun _ _ _ _ => rfl
  votesHeldSet_eq := fun _ _ => rfl
  ac_valid_payload_eq := fun _ _ => rfl
  included_votes_eq := fun _ _ => rfl
  included_support_votes_eq := fun _ _ => rfl
  is_live_eq := fun _ _ _ => rfl
  is_locked_eq := fun _ _ _ => rfl
  live_lock_vetoes_eq := fun _ _ _ => rfl
  votes_by_eq := fun _ _ => rfl
  equivocates_eq := fun _ _ => rfl
  participates_eq := fun _ _ => rfl
  no_second_vote_in_eq := fun _ _ => rfl
  equivocators_eq := fun _ => rfl
  participants_eq := fun _ => rfl
  voters_count_eq := fun _ => rfl
  viable_tree_eq := fun _ _ => rfl
  get_anchor_eq := by intros; rfl
  live_entries_eq := fun _ _ => rfl
  saved_extends_eq := fun n s'' B =>
    GoldilocksCorrectness.Proofs.Routines.saved_extends_eq n.A (Goldilocks.fg_to_ac n.S) s'' B
  slow_test_eq := fun _ _ _ _ => rfl
  ac_confirmed_eq := by
    intro n
    show Goldilocks.ac_confirmed n.A (Goldilocks.fg_to_ac n.S) = _
    simp only [Goldilocks.ac_confirmed, Id.run]
    rfl
  awake_since_eq := by
    rintro ⟨v, t, S, A, Λ, aw⟩ t₀
    cases aw <;> rfl
  attestation_well_formed_iff := fun a =>
    GoldilocksCorrectness.Proofs.Routines.attestation_well_formed_iff a
  block_well_formed_iff := fun P X B =>
    GoldilocksCorrectness.Proofs.Routines.block_well_formed_iff P X B
  present_eq := fun _ => rfl
  advance_eq := by
    intro Φ old C?
    show Goldilocks.advance Φ old C? = _
    cases C? with
    | none =>
        simp [Goldilocks.advance, Id.run]
        rfl
    | some C =>
        simp [Goldilocks.advance, Id.run]
        rfl
  slots_before_eq := fun _ _ => rfl

end GoldilocksCorrectness.Record
