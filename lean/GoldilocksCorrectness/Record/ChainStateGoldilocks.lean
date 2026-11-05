module
public import GoldilocksCorrectness.Record.ChainStateFacts
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Proofs.Routines.FinalityPair
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
import all Goldilocks.FG.ChainState

@[expose] public section

/-!
# The spec's chain-state facts

`chainStateFacts_goldilocks`: the spec's model satisfies `ChainStateFacts`. Each field is the
library's theorem it restates: at `Model.goldilocks` every member is the spec's routine, so the
field's statement is the theorem's. A field over a non-genesis block `B` and its parent's chain
state is the theorem at the parent's chain state, once `B` is split into its constructor (the
chain state of `.node p …` is, by definition, the state transition from `p`'s). A field reading a
certificate is the theorem once the record's certificate is read as the landed one at the spec's
model (`goldilocks_JustificationCertOn`, `goldilocks_ProgressCertOn`,
`goldilocks_FinalityCertOn`). The fields written for the record hold by definition (this page
sees the spec's chain-state bodies).
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the facts about the chain state of a block.

Read aloud: Goldilocks' chain states of blocks satisfy every fact the record asks of a model's. -/
theorem chainStateFacts_goldilocks : ChainStateFacts (Model.goldilocks (V := V)) where
  lem47a_state_transition_bounds := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.lem47a_state_transition_bounds V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  lem47b_state_transition_height := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.lem47b_state_transition_height V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  lem47c_state_transition_T_h := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.lem47c_state_transition_T_h V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  state_transition_justification := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.state_transition_justification V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  valid_attestation_of_height := @GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_height V
  state_transition_h_F_mono := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.state_transition_h_F_mono V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  quorum_certificate_with_counted := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.quorum_certificate_with_counted V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  valid_attestation_cases := @GoldilocksCorrectness.Proofs.Routines.valid_attestation_cases V
  valid_attestation_of_pending := @GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_pending V
  chainStateOf_bounds := @GoldilocksCorrectness.Proofs.Routines.chainStateOf_bounds V _ _
  chainStateOf_pending_above := @GoldilocksCorrectness.Proofs.Routines.chainStateOf_pending_above V _ _
  counted_kept_of_same_height := @GoldilocksCorrectness.Proofs.Routines.counted_kept_of_same_height V _ _
  chainStateOf_genesis_h := @GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_h V _ _
  chainStateOf_genesis_T_h := @GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_T_h V _ _
  chainStateOf_genesis_J := @GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_J V _ _
  pending_pair_step := by
    intro C B hB
    cases B with
    | genesis => exact absurd rfl hB
    | node p s r votes support ats v =>
        exact @GoldilocksCorrectness.Proofs.Routines.pending_pair_step V _ _ C
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C p)
          (.node p s r votes support ats v)
  first_advance_justified_or_timeout := @GoldilocksCorrectness.Proofs.Routines.first_advance_justified_or_timeout V _ _
  justification_witness_of_finalized := @GoldilocksCorrectness.Proofs.Routines.justification_witness_of_finalized V _ _
  lem66_chain_state_certified := by
    simp only [← Statements.Routines.goldilocks_JustificationCertOn, ← Statements.Routines.goldilocks_FinalityCertOn]
    exact @GoldilocksCorrectness.Proofs.Routines.lem66_chain_state_certified V _ _
  lem67b_first_advance_cases := by
    simp only [← Statements.Routines.goldilocks_JustificationCertOn, ← Statements.Routines.goldilocks_ProgressCertOn]
    exact @GoldilocksCorrectness.Proofs.Routines.lem67b_first_advance_cases V _ _
  chainStateOf_F_genesis := @GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis V _ _
  round_justified_of_spacing3 := @GoldilocksCorrectness.Proofs.Routines.round_justified_of_spacing3 V _ _
  lem93_block_finalizes_pending := @GoldilocksCorrectness.Proofs.Routines.lem93_block_finalizes_pending V _ _
  on_chain_counted := @GoldilocksCorrectness.Proofs.Routines.on_chain_counted V _ _
  chainStateOf_pending_last := by
    intro C X hlt
    obtain ⟨l, hl⟩ := GoldilocksCorrectness.Proofs.Routines.chainStateOf_pending_last C X hlt
    exact ⟨l, _, hl, rfl, rfl⟩
  cs_initial_eq := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩
  newest_eq := fun _ _ => rfl
  is_pending_eq := fun _ _ => rfl

end GoldilocksCorrectness.Record
