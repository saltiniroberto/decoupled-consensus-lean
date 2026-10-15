import Proofs.Instance.Members.Base

/-!
# The members of the duties, the tick and the node

The definitions of the namespace `SpecDraftRecord.Member` that fill the duty, tick and node members
of the record `Model V` with the spec's routines, one definition per member, named as the member.
-/

set_option autoImplicit false

namespace SpecDraftRecord.Member

open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The environment given to `Config.toSpec` where no environment is read: delay one, `t_GST = 0`,
    every committee empty and every weight `1`. -/
def unreadEnvForDuties [Inhabited V] : DecoupledConsensusModel.Env V where
  Δ := 1
  Δ_pos := Int.one_pos
  t_GST := 0
  t_GST_nonneg := le_refl 0
  proposer := fun _ => default
  committees := ⟨fun _ => ∅⟩
  electorate := ⟨fun _ => 1, fun _ => Nat.one_pos⟩

/-- The values supplied from outside, read from the node `nd`: the root of the block proposed in
    slot `s` is the image of `nd.new_root s`. -/
def externalOfNode (nd : DecoupledConsensusModel.Protocol.Node V) : Spec.External V where
  new_root := fun _ s => Spec.BlockId.toSpec (nd.new_root s)

/-- The first block in the list `sent` of objects a duty sent, if there is one. -/
def firstSentBlock (sent : List (Spec.NamedObject V)) :
    Option (Spec.Block V) :=
  sent.findSome? fun
    | .block B => some B
    | _ => none

/-- The first Goldfish vote in the list `sent` of objects a duty sent, if there is one. -/
def firstSentGoldfishVote (sent : List (Spec.NamedObject V)) :
    Option (Spec.GoldfishVote V) :=
  sent.findSome? fun
    | .gfVote vote => some vote
    | _ => none

/-- The first attestation in the list `sent` of objects a duty sent, if there is one. -/
def firstSentAttestation (sent : List (Spec.NamedObject V)) :
    Option (Spec.Attestation V) :=
  sent.findSome? fun
    | .attest a => some a
    | _ => none

/-! ## The duties and the tick -/

/-- Record member `duties_propose_block_with`: the spec's `Protocol.propose_block` for the validator
    `nd.val_index` on the store `st` with its saved grades read from `c`. An outcome is the store
    after the duty, holding the saved grades `c`, with the block the duty broadcast, if any; there
    is none when the routine fails. -/
def duties_propose_block_with (c : Spec.SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V) :
    DC.NDRE (Spec.Store V × Option (DecoupledConsensusModel.NamedBlock V)) :=
  successOutcomes
    (((Spec.Protocol.propose_block (Spec.Config.toSpec E hc cfg)
        (Spec.Provisional.toSpec E) (externalOfNode nd) nd.val_index
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc cfg).round_of st.s)) }
        ).run []).map
      fun out => ({ out.1 with saved_grades := c },
        (firstSentBlock out.2).map Spec.Block.toProofNamed))

/-- Record member `duties_attest_with`: the spec's `Protocol.attest` for the validator
    `nd.val_index` on the store `st` with its saved grades read from `c` and the signing history
    `sh`. An outcome is the store and the signing history after the duty, with the attestation it
    broadcast. -/
def duties_attest_with (c : Spec.SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V)
    (sh : Spec.SigningHistory) :
    DC.NDRE (Spec.Store V × Spec.SigningHistory ×
      DecoupledConsensusModel.NamedAttestation V) :=
  successOutcomes (do
    let out ← (Spec.Protocol.attest (Spec.Config.toSpec E hc unreadHeightConfig)
        nd.val_index { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        sh).run []
    let a ← firstSentAttestation out.2
    return ({ out.1.1 with saved_grades := c }, out.1.2, a.toProofNamed))

/-- Record member `duties_update_confirmation_with`: the spec's `Protocol.update_confirmation` for
    slot `s` on the store `st` with its saved grades read from `c`; an outcome is the store after
    the confirmation. -/
def duties_update_confirmation_with (c : Spec.SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Spec.Store V) (s : DecoupledConsensusModel.Slot) :
    DC.NDRE (Spec.Store V) :=
  successOutcomes
    ((Spec.Protocol.update_confirmation (Spec.Config.toSpec E hc unreadHeightConfig)
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        s).map
      fun out => { out with saved_grades := c })

/-- Record member `inWindow`: the spec's `Protocol.in_admission_window`, whether round `r` is in the
    admission window of `st` under the round schedule `hc`. -/
def inWindow [Inhabited V] (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Spec.Store V) (r : DecoupledConsensusModel.Round) : Bool :=
  Spec.Protocol.in_admission_window
    (Spec.Config.toSpec (unreadEnvForDuties (V := V)) hc unreadHeightConfig) st r

/-- Record member `round_action_with`: the spec's `Protocol.build_attestation` for the validator
    `nd.val_index` on the store `st` with its saved grades read from `c` and the signing history
    `sh`. An outcome is the signing history after signing with the attestation built. -/
def round_action_with (c : Spec.SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V)
    (sh : Spec.SigningHistory) :
    DC.NDRE (Spec.SigningHistory × DecoupledConsensusModel.NamedAttestation V) :=
  successOutcomes
    ((Spec.Protocol.build_attestation
        (Spec.Config.toSpec E hc unreadHeightConfig) nd.val_index
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        sh).map
      fun out => (out.1, out.2.toProofNamed))

/-- Record member `duties_goldfish_vote_with`: the spec's `Protocol.goldfish_vote` for the validator
    `nd.val_index` on the store `st` with its saved grades read from `c`. An outcome is the store
    after the duty, holding the saved grades `c`, with the Goldfish vote it broadcast, if any. -/
def duties_goldfish_vote_with (c : Spec.SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V) :
    DC.NDRE (Spec.Store V × Option (DecoupledConsensusModel.GoldfishVote V)) :=
  successOutcomes
    (((Spec.Protocol.goldfish_vote (Spec.Config.toSpec E hc unreadHeightConfig)
        (Spec.Provisional.toSpec E) nd.val_index
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
              (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
          ).run []).map
      fun out => ({ out.1 with saved_grades := c },
        (firstSentGoldfishVote out.2).map Spec.GoldfishVote.toProof))

/-- Record member `grade2_block_with`: the spec's `Protocol.grade2_block_with` for round `r` on the
    store `st` with its saved grades read from `c`; the outcomes are round `r`'s grade-2 blocks. -/
def grade2_block_with (c : Spec.SavedGrades V) (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Spec.Store V)
    (r : DecoupledConsensusModel.Round) : DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes
    ((Spec.Protocol.grade2_block_with
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) r) }
      r).map
      (Option.map Spec.Block.toProof))

/-- Record member `proposal_with`: the spec's `Protocol.build_proposal` for the validator
    `nd.val_index` on the store `st` with its saved grades read from `c`; an outcome is `some` of
    the proposed block. -/
def proposal_with (c : Spec.SavedGrades V)
    (_source : DecoupledConsensusModel.Protocol.ProposalRowSource)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V) :
    DC.NDRE (Option (DecoupledConsensusModel.NamedBlock V)) :=
  successOutcomes
    ((Spec.Protocol.build_proposal (Spec.Config.toSpec E hc unreadHeightConfig)
        (externalOfNode nd) nd.val_index
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
              (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
          ).map
      fun B => some B.toProofNamed)

/-- Record member `select`: the spec's `Protocol.attestations_to_include` on `st` under the round
    schedule `hc`, the attestations a proposal from `st` includes. The source is not read. -/
def select [Inhabited V] (_source : DecoupledConsensusModel.Protocol.ProposalRowSource)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Spec.Store V) :
    DC.NDRE (List (DecoupledConsensusModel.NamedAttestation V)) :=
  successOutcomes
    ((Spec.Protocol.attestations_to_include
        (Spec.Config.toSpec (unreadEnvForDuties (V := V)) hc unreadHeightConfig) st).map
      (List.map Spec.Attestation.toProofNamed))

/-- Record member `parentBody?`: the spec's `blockWithRoot` on the tree `st.T` at the root of `B`,
    `some` of the block of the tree with that root, or `none` when the tree holds none. There is no
    outcome when two blocks of the tree have that root. -/
def parentBody? (st : Spec.Store V) (B : DecoupledConsensusModel.Block V) :
    DC.NDRE (Option (DecoupledConsensusModel.NamedBlock V)) :=
  successOutcomes
    ((Spec.blockWithRoot st.T (Spec.BlockId.toSpec B.root)).map
      (Option.map Spec.Block.toProofNamed))

/-- Record member `proposalRows`: the spec's `Protocol.proposal_attestations`, the attestations of
    `rows` that a proposal on `P` includes. -/
def proposalRows (P : DecoupledConsensusModel.NamedBlock V)
    (rows : List (DecoupledConsensusModel.NamedAttestation V)) :
    List (DecoupledConsensusModel.NamedAttestation V) :=
  (Spec.Protocol.proposal_attestations (Spec.Block.toSpecNamed P)
      (rows.map Spec.Attestation.toSpecNamed)).map Spec.Attestation.toProofNamed

/-- Record member `fg_source_with`: the spec's `Protocol.fg_source_with` for round `r` and the
    grade-2 candidate `A_G2`, read as a block of `st`'s tree by `Store.blockOfImage`, on the store
    `st` with its saved grades read from `c`. -/
def fg_source_with (c : Spec.SavedGrades V) (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Spec.Store V)
    (r : DecoupledConsensusModel.Round) (A_G2 : Option (DecoupledConsensusModel.Block V)) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes
    ((Spec.Protocol.fg_source_with
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) r) }
      r
        (A_G2.map st.blockOfImage)).map
      (Option.map Spec.Block.toProof))

/-- Record member `get_sg_vote_with`: the spec's `Protocol.get_sg_vote_with` for round `r` and the
    grade-2 candidate `A_G2` on the store `st` with its saved grades read from `c`; the outcomes are
    round `r`'s SG votes. -/
def get_sg_vote_with (c : Spec.SavedGrades V) (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Spec.Store V)
    (r : DecoupledConsensusModel.Round) (A_G2 : Option (DecoupledConsensusModel.Block V)) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes
    ((Spec.Protocol.get_sg_vote_with
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) r) }
      r
        (A_G2.map Spec.Block.toSpec)).map Spec.Block.toProof)

/-- Record member `processedRows`: the spec's `Protocol.all_attestations`, the attestations of `st`
    of every round up to the store's round. -/
def processedRows [Inhabited V] (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Spec.Store V) : List (DecoupledConsensusModel.NamedAttestation V) :=
  (Spec.Protocol.all_attestations
      (Spec.Config.toSpec (unreadEnvForDuties (V := V)) hc unreadHeightConfig) st).map
    Spec.Attestation.toProofNamed

/-- Record member `with_proposal_input`: `use` applied to the spec's `Protocol.proposal_input` for
    the validator `nd.val_index` on the store `st` with its saved grades read from `c`. -/
def with_proposal_input {Result : Type} (c : Spec.SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V)
    (use : DecoupledConsensusModel.Protocol.ProposalInput V → Result) : DC.NDRE Result :=
  successOutcomes
    ((Spec.Protocol.proposal_input (Spec.Config.toSpec E hc unreadHeightConfig)
        (externalOfNode nd) nd.val_index
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
              (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
          ).map
      fun input => use input.toProof)

/-- Record member `creatorInput`: the signing record's input with the fields of `input`. -/
def creatorInput (input : DecoupledConsensusModel.Protocol.AttestationInput V) :
    DecoupledConsensusModel.Protocol.NamedRecord.Input V :=
  DecoupledConsensusModel.Protocol.NamedActions.creatorInput input

/-- Record member `get_fg_vote_with`: the spec's `Protocol.get_fg_vote_with` for round `r` and the
    grade-2 candidate `A_G2`, read as a block of `st`'s tree by `Store.blockOfImage`, on the store
    `st` with its saved grades read from `c`. It has no outcome when `r` is neither the store's
    round nor the next one. -/
def get_fg_vote_with (c : Spec.SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Spec.Store V)
    (r : DecoupledConsensusModel.Round) (A_G2 : Option (DecoupledConsensusModel.Block V)) :
    DC.NDRE (Option (DecoupledConsensusModel.Height × DecoupledConsensusModel.BlockId × Bool) ×
      DecoupledConsensusModel.Height × DecoupledConsensusModel.BlockId ×
      DecoupledConsensusModel.Height) :=
  successOutcomes
    ((Spec.Protocol.get_fg_vote_with (Spec.Config.toSpec E hc unreadHeightConfig)
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        r (A_G2.map st.blockOfImage)).map
      fun out => (out.1.map fun f => (f.1, f.2.1.toProof, f.2.2),
        out.2.1, out.2.2.1.toProof, out.2.2.2))

/-- Record member `chainRows`: the spec's `Protocol.attestations_on_chain`, the attestations
    included in `B` or one of its ancestors. -/
def chainRows (B : DecoupledConsensusModel.NamedBlock V) :
    List (DecoupledConsensusModel.NamedAttestation V) :=
  (Spec.Protocol.attestations_on_chain (Spec.Block.toSpecNamed B)).map
    Spec.Attestation.toProofNamed

/-- Record member `with_attestation_input`: `use` applied to the spec's `Protocol.attestation_input`
    for the validator `nd.val_index` on the store `st` with its saved grades read from `c`. -/
def with_attestation_input {Result : Type} (c : Spec.SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V)
    (use : DecoupledConsensusModel.Protocol.AttestationInput V → Result) : DC.NDRE Result :=
  successOutcomes
    ((Spec.Protocol.attestation_input
        (Spec.Config.toSpec E hc unreadHeightConfig) nd.val_index
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        ).map
      fun input => use input.toProof)

/-- Record member `carriedRows`: the spec's `Protocol.included_attestations_in_window`, the
    attestations in the admission window included in an eligible block of `st`. -/
def carriedRows [Inhabited V] (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Spec.Store V) : DC.NDRE (List (DecoupledConsensusModel.NamedAttestation V)) :=
  successOutcomes
    ((Spec.Protocol.included_attestations_in_window
        (Spec.Config.toSpec (unreadEnvForDuties (V := V)) hc unreadHeightConfig) st).map
      (List.map Spec.Attestation.toProofNamed))

/-- Record member `eligibleBody`: the spec's `Protocol.may_repropose_attestations_of`, whether `B`'s
    round is in `st`'s admission window and `B`'s attestations are admissible. -/
def eligibleBody [Inhabited V] (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Spec.Store V) (B : DecoupledConsensusModel.NamedBlock V) : Bool :=
  Spec.Protocol.may_repropose_attestations_of
    (Spec.Config.toSpec (unreadEnvForDuties (V := V)) hc unreadHeightConfig) st
    (Spec.Block.toSpecNamed B)

/-- Record member `orderedBodies`: the spec's `Protocol.sorted_blocks`, the blocks of `st` ordered
    by root; there is no outcome when two blocks share a root. -/
def orderedBodies (st : Spec.Store V) :
    DC.NDRE (List (DecoupledConsensusModel.NamedBlock V)) :=
  successOutcomes
    ((Spec.Protocol.sorted_blocks st).map
      (List.map Spec.Block.toProofNamed))

/-- Record member `poolRows`: the spec's `Protocol.attestations_in_window`, the attestations of `st`
    whose round is in the admission window. -/
def poolRows [Inhabited V] (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Spec.Store V) : List (DecoupledConsensusModel.NamedAttestation V) :=
  (Spec.Protocol.attestations_in_window
      (Spec.Config.toSpec (unreadEnvForDuties (V := V)) hc unreadHeightConfig) st).map
    Spec.Attestation.toProofNamed

/-! ## The node -/

/-- Record member `st`: the store of `n`. -/
def st (n : Spec.NodeState V) : Spec.Store V := n.st

/-- Record member `record`: the signing history of `n`. -/
def record (n : Spec.NodeState V) : Spec.SigningHistory := n.signingHistory

/-- Record member `cache`: the saved grades of `n`'s store. -/
def cache (n : Spec.NodeState V) : Spec.SavedGrades V := n.st.saved_grades

/-- Record member `gradeContract`: the identity on saved grades. -/
def gradeContract (c : Spec.SavedGrades V) : Spec.SavedGrades V := c

/-- Record member `contractCache`: the identity on saved grades. -/
def contractCache (k : Spec.SavedGrades V) : Spec.SavedGrades V := k

/-- Record member `initial`: the spec's `initial` node state of validator `v` under the parameters
    of setup `S`. -/
def initial (S : DecoupledConsensusModel.Execution.Setup V) (v : V) : Spec.NodeState V :=
  Spec.initial (Setup.toSpec S).C v

/-- Record member `wake`: the spec's `wake`, which erases `awakeSince` and keeps the rest of the
    node state. -/
def wake (n : Spec.NodeState V) : Spec.NodeState V := Spec.wake n

/-- Record member `tick`: the spec's `tick` of the node state `n` at time `t` under setup `S`; an
    outcome is the new node state with the objects broadcast, in order. The validator `v` is not
    read. -/
def tick (S : DecoupledConsensusModel.Execution.Setup V) (_v : V) (n : Spec.NodeState V)
    (t : Int) :
    DC.NDRE (Spec.NodeState V × List (DecoupledConsensusModel.Execution.NamedObject V)) :=
  successOutcomes
    (((Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X n t).run []).map
      fun out => (out.1, out.2.map Spec.NamedObject.toProof))

/-- Record member `process`: the spec's dispatch `Spec.Sts.receive` of the object `o` on `n`, at the
    parameters read from `S`. It has exactly one outcome, since the receiving routines never fail. -/
def process (S : DecoupledConsensusModel.Execution.Setup V) (n : Spec.NodeState V)
    (o : DecoupledConsensusModel.Execution.NamedObject V) : DC.NDRE (Spec.NodeState V) :=
  pure (receiveNamedObject S n o)

/-- Record member `postCore`: the store `st` after it admits the block `B`, its attestations not yet
    admitted (`Handlers.admitBlockCore`); the store is unchanged when it does not accept `B`. -/
def postCore (S : DecoupledConsensusModel.Execution.Setup V) (st : Spec.Store V)
    (B : DecoupledConsensusModel.NamedBlock V) : Spec.Store V :=
  Handlers.admitBlockCore (Spec.Config.toSpec S.E S.hc S.cfg)
    (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B)

/-- Record member `receipt_process`: the store `st` after it admits the object `o` with the routine
    of `o`'s kind: `Protocol.on_block`, `Protocol.on_goldfish_vote_checked` or
    `Protocol.admit_attestation`. Unlike the receiving routines, it does not apply
    `make_grades_compatible_with_finalized` afterwards. -/
def receipt_process (S : DecoupledConsensusModel.Execution.Setup V) (st : Spec.Store V) :
    DecoupledConsensusModel.Execution.NamedObject V → Spec.Store V
  | .block B =>
      Spec.Protocol.on_block (Spec.Config.toSpec S.E S.hc S.cfg)
        (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B)
  | .gfVote u =>
      Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec S.E) st
        (Spec.GoldfishVote.toSpec u)
  | .attest a =>
      Spec.Protocol.admit_attestation (Spec.Config.toSpec S.E S.hc S.cfg)
        st (Spec.Attestation.toSpecNamed a)

/-- Record member `mkNode`: the node state with the store `st` holding the saved grades `c`, the
    signing history `sh`, the default validator, and `awakeSince` equal to `none`. -/
def mkNode [Inhabited V] (st : Spec.Store V) (sh : Spec.SigningHistory)
    (c : Spec.SavedGrades V) : Spec.NodeState V :=
  { v := default, st := { st with saved_grades := c }, signingHistory := sh, awakeSince := none }

/-- Record member `wakeEvents`: `true`, since the spec's wake changes the node state. -/
def wakeEvents : Bool := true

/-- Record member `runs_as`: the node state `n` runs as the validator `v` when `n.v = v`. -/
def runs_as (n : Spec.NodeState V) (v : V) : Prop := n.v = v

/-- Record member `awake_for_grade1`: the node `n` has been awake since the grade-1 window start of
    round `r` or earlier, the test the tick applies before round `r`'s proposal and Goldfish vote.
    The validator `v` is not read. -/
def awake_for_grade1 (S : DecoupledConsensusModel.Execution.Setup V) (_v : V)
    (n : Spec.NodeState V) (r : DecoupledConsensusModel.Round) : Prop :=
  ∃ a, n.awakeSince = some a ∧ a ≤ Spec.grade1_window_start (Setup.toSpec S).C r

/-- Record member `awake_for_grade2`: the node `n` has been awake since the grade-2 window start of
    round `r` or earlier, the test the tick applies before round `r`'s confirmation and attestation.
    The validator `v` is not read. -/
def awake_for_grade2 (S : DecoupledConsensusModel.Execution.Setup V) (_v : V)
    (n : Spec.NodeState V) (r : DecoupledConsensusModel.Round) : Prop :=
  ∃ a, n.awakeSince = some a ∧ a ≤ Spec.grade2_window_start (Setup.toSpec S).C r

/-- Record member `make_grades_compatible_with_finalized`: the spec's routine of that name, the
    store `st` with every block of its saved grades replaced by its deepest ancestor compatible with
    the store's finalized block. -/
def make_grades_compatible_with_finalized (st : Spec.Store V) :
    Spec.Store V :=
  Spec.make_grades_compatible_with_finalized st

/-- Record member `store_with_cache`: the store `st` with its saved grades replaced by `c`. -/
def store_with_cache (st : Spec.Store V) (c : Spec.SavedGrades V) :
    Spec.Store V :=
  { st with saved_grades := c }

end SpecDraftRecord.Member
