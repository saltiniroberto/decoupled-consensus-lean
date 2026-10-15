module
public import Proofs.Vocabulary.Generic.SlotFreshness
public import Proofs.Vocabulary.Execution.StoreFinalityCore
public import Proofs.Vocabulary.Protocol.Duties.Proposals.ProposalRows
public import Proofs.Vocabulary.Protocol.Evidence.ProvenanceBridge
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedActions_proposal_with
public import Proofs.Vocabulary.ModelProperties.with_proposal_input
public import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.get_sg_root_with
public import Proofs.Vocabulary.ModelProperties.carried_attestations_admissible
public import Proofs.Vocabulary.ModelProperties.NamedAttestation_erase
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Proofs.Vocabulary.ModelProperties.NamedBlock_parent

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Totality -/

/-- The named-store root invariant holds at the proposer's read for slot `s`. -/
theorem proposerReadAt_invariant (S : Setup V) (rho : Run V) (s : Slot) :
    Proofs.NamedStoreRoots.Invariant S.E S.cfg (proposerReadAt S rho s).st :=
  by
    show Proofs.NamedStoreRoots.Invariant S.E S.cfg
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s))
        (Protocol.proposal_time S.E s)).st
    rw [Proofs.ModelProperties.confirmationReadFrom_st]
    exact Proofs.NamedStoreRoots.invariant_clock S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s)).st
      (Protocol.proposal_time S.E s)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.proposal_time S.E s) (S.E.proposer s)).1.1


/-- The proposal computed at slot `s` always exists. -/
theorem proposedBlockAt_isSome (S : Setup V) (rho : Run V) (s : Slot) :
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B :=
  Proofs.ModelProperties.proposal_with_gradeContract_isSome (proposerReadAt S rho s).cache
    .poolAndCarried S.E S.hc S.cfg (S.node (S.E.proposer s))
    (proposerReadAt S rho s).st (proposerReadAt_invariant S rho s)


/-- The selected parent is in the core tree of the proposer's read. -/
theorem proposedParent_mem (S : Setup V) (rho : Run V) (s : Slot) :
    proposedParent S rho s ∈ (proposerReadAt S rho s).st.core.T :=
  by
    show (Protocol.with_proposal_input
      (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc
      (S.node (S.E.proposer s)) (proposerReadAt S rho s).st.core.toHealing id).parent ∈ _
    rw [Proofs.ModelProperties.with_proposal_input_id_parent]
    have hroot := Proofs.NamedStoreRoots.fg_root_mem _ (proposerReadAt_invariant S rho s).2
    have hanchor : ((NamedProfile.gradeContract (proposerReadAt S rho s).cache).read S.E S.hc
        (proposerReadAt S rho s).st.core.toHealing
        (S.hc.round_of (proposerReadAt S rho s).st.core.toHealing.s)).anchor ∈
        (proposerReadAt S rho s).st.core.toHealing.T := by
      rw [Proofs.ModelProperties.gradeContract_read_anchor]
      exact NamedProposalParent.frame_anchor_mem S.E S.hc _ _ _
        (by rw [Proofs.ModelProperties.toHealing_T]; exact hroot)
    rw [← Proofs.ModelProperties.toHealing_T]
    exact NamedProposalParent.get_head_with_mem _ S.E S.hc _ _ _ _ hanchor


/-! ## The fields of the proposal -/

/-- The proposal computed at slot `s` is of slot `s`. -/
theorem proposedBlockAt_slot (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) : B.slot = s :=
  Proofs.Optimistic.proposedBlockAt_slot S rho s hB


/-- The proposal computed at slot `s` names the slot-`s` proposer `S.E.proposer s`. -/
theorem proposedBlockAt_proposer (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) : B.proposer? = some (S.E.proposer s) := by
  have hpay := Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract
    (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  rw [hpay.2.2.2.2.2.2.2]
  show some (Protocol.with_proposal_input
      (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc
      (S.node (S.E.proposer s)) (proposerReadAt S rho s).st.core.toHealing id).proposer = _
  rw [Proofs.ModelProperties.with_proposal_input_id_proposer]
  exact congrArg some (S.node_val_index (S.E.proposer s))


/-- The proposal's named parent erases to the selected parent `proposedParent S rho s`. -/
theorem proposedBlockAt_parent (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) :
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧ p.erase = proposedParent S rho s := by
  exact Proofs.ModelProperties.proposal_with_parent?
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB


/-! ## The honest proposer's tick -/

/-- An honest slot-`s` proposer, with `s > 0` and the proposal time within the horizon, emits the
    proposal computed at slot `s` at that time. -/
theorem proposedBlockAt_emits_of_honest (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon) :
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧ B.slot = s ∧
      NamedRun.emits S rho (S.E.proposer s) (.block B)
        (Protocol.proposal_time S.E s) := by
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho s
  obtain ⟨hslot, hemit⟩ := Proofs.Optimistic.proposalTick S sch s hs hprop hhor hB
  exact ⟨B, hB, hslot, hemit⟩

omit [Fintype V] in
private theorem admit_rows_bodies (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rest ih =>
    show (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rest).bodies = st.bodies
    rw [ih, NamedAdmission.admit_row_bodies]

/-- A block whose named parent is held, whose erasure is new to the core tree, and whose erasure the
    checked handler inserts is retained as a named body. -/
theorem mem_bodies_on_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hp : B.parent ∈ st.bodies) (hnew : B.erase ∉ st.core.T)
    (hins : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B.erase
        (fun parentState => Protocol.named_transition E cfg parentState B)) hc st.core
      B.erase).T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).bodies := by
  have hcore : (Protocol.NamedStore.process_block_core E hc cfg st B).bodies =
      insert B st.bodies := by
    show (if B.parent ∉ st.bodies then st else
      Protocol.NamedStore.commitBlock st _ B).bodies = insert B st.bodies
    rw [if_neg (not_not.mpr hp), Protocol.NamedStore.commitBlock,
      if_pos (And.intro hnew hins)]
  have hmem : B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies := by
    rw [hcore]; exact Finset.mem_insert_self _ _
  show B ∈ (Protocol.NamedAdmission.admit_carried .alsoCarried hc st
    (Protocol.NamedStore.process_block_core E hc cfg st B) B).bodies
  dsimp only [Protocol.NamedAdmission.admit_carried]
  split
  · rw [admit_rows_bodies]; exact hmem
  · exact hmem

/-- A computed proposal whose erasure is new and inserted by the checked handler is retained as a
    named body of the proposer's read. -/
theorem proposedBlockAt_on_block_with_bodies (S : Setup V) (rho : Run V) (s : Slot)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hnew : B.erase ∉ (proposerReadAt S rho s).st.core.T)
    (hins : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc (proposerReadAt S rho s).st.core B.erase).T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies :=
  mem_bodies_on_block_with S.E S.hc S.cfg (proposerReadAt S rho s).st B
    (Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB).1
    hnew hins

private theorem tick_bodies_proposal (S : Setup V) (v : V) (n : NodeState V) (s : Slot)
    (hs : 0 < s) (hpr : S.E.proposer s = (S.node v).val_index) :
    (Execution.NamedNode.tick S v n (Protocol.proposal_time S.E s)).1.st.bodies =
      (Protocol.NamedDuties.propose_block_with
        (NamedProfile.gradeContract (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).cache) S.E S.hc S.cfg (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).st).1.bodies := by
  have hslot : S.E.slotOf (Protocol.proposal_time S.E s) = s :=
    Proofs.Optimistic.slotOf_proposal_time S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock,
    Proofs.Optimistic.proposal_time_ne_vote_time S.E s,
    Proofs.Optimistic.proposal_time_ne_support_cutoff S.E s, hpr, hs,
    and_false, and_true, if_false, if_true, Protocol.NamedDuties.attest_with,
    Protocol.NamedAdmission.admit_row]
  split
  · split <;> rfl
  · rfl

/-- An honest proposer that admits its slot-`s` proposal holds it as a named body right after its
    proposal tick. -/
theorem proposedBlockAt_mem_bodies_after_tick (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hadmit : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies) :
    ∃ i : Nat, rho.events[i]? =
        some (.tick (S.E.proposer s) (Protocol.proposal_time S.E s)) ∧
      B ∈ (NamedRun.stateBefore S rho (i + 1) (S.E.proposer s)).st.bodies := by
  obtain ⟨-, i, hi, -⟩ := Proofs.Optimistic.proposalTick S sch s hs hprop hhor hB
  refine ⟨i, hi, ?_⟩
  have hst : NamedRun.stateBefore S rho i (S.E.proposer s) =
      NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s) :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hi
  rw [Proofs.NamedRuntime.stateBefore_tick S rho hi, hst,
    tick_bodies_proposal S (S.E.proposer s)
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s)) s hs
      (S.node_val_index (S.E.proposer s)).symm]
  have hB' : Protocol.NamedActions.proposal_with
      (NamedProfile.gradeContract (proposerReadAt S rho s).cache) .poolAndCarried
      S.E S.hc (S.node (S.E.proposer s)) (proposerReadAt S rho s).st = some B := hB
  show B ∈ (Protocol.NamedDuties.propose_block_with
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc S.cfg
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st).1.bodies
  simp only [Protocol.NamedDuties.propose_block_with, hB']
  exact hadmit

/-- The proposal computed at slot `s` is unique. -/
theorem proposedBlockAt_unique (S : Setup V) (rho : Run V) (s : Slot)
    {B B' : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hB' : proposedBlockAt S rho s = some B') : B = B' :=
  Option.some.inj (hB ▸ hB')


/-! ## Admission before a cutoff, over a named block -/

/-- `v` accepted the named block `B` at some time before `Gamma`. -/
def NamedAdmittedBefore (S : Setup V) (rho : Run V) (v : V) (B : NamedBlock V)
    (Gamma : Time) : Prop :=
  ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S rho i v (Object.block B) t ∧ t < Gamma


#print axioms proposerReadAt_invariant
#print axioms proposedBlockAt_isSome
#print axioms proposedBlockAt_slot
#print axioms proposedBlockAt_proposer
#print axioms proposedBlockAt_parent
#print axioms proposedBlockAt_emits_of_honest
#print axioms mem_bodies_on_block_with
#print axioms proposedBlockAt_on_block_with_bodies
#print axioms proposedBlockAt_mem_bodies_after_tick
#print axioms proposedBlockAt_unique


/-! ## The frame contract's anchor and the FG root -/

/-- The FG root is an ancestor of the frame contract's anchor `get_sg_root_with` at round `r`. -/
theorem fg_root_preceq_get_sg_root_with_frame (c : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract c) E hc st r) := by
  show Block.Preceq (Protocol.get_fg_root st.toFG)
    (DecoupledConsensusModel.Protocol.anchor E hc st r (DecoupledConsensusModel.Protocol.readFrame c st r).g1)
  unfold DecoupledConsensusModel.Protocol.anchor
  match hg : (DecoupledConsensusModel.Protocol.readFrame c st r).g1 with
  | none => exact Block.preceq_self _
  | some none => exact Block.preceq_self _
  | some (some root) =>
    cases ha : DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree st.toFG) root with
    | none => simpa only [ha, Option.getD_none, Block.Preceq] using Block.preceq_self _
    | some A =>
      have hA : A ∈ (Protocol.get_filtered_block_tree st.toFG).filter
          (fun B => Block.preceq B root = true) := Proofs.Engine.deepest?_mem ha
      simpa only [ha, Option.getD_some, Block.Preceq] using
        Proofs.Records.preceq_get_fg_root_of_mem_filtered (Finset.mem_filter.mp hA).1

/-- Every contract's anchor is an ancestor of the head it walks to. -/
theorem get_sg_root_with_preceq_get_head_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Block.Preceq (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
      (Protocol.get_head_with contract E hc st votes support k) :=
  Protocol.ghost_preceq _ _ _ _


/-- The finalized block of the proposer's read at slot `s` is an ancestor of the selected parent. -/
theorem finalized_preceq_proposedParent (S : Setup V) (rho : Run V) (s : Slot) :
    Block.Preceq (proposerReadAt S rho s).st.core.F (proposedParent S rho s) := by
  have hcore : (proposerReadAt S rho s).st.core = Proofs.Optimistic.tickStore S
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s)).st.core
      (Protocol.proposal_time S.E s) :=
    Proofs.ModelProperties.confirmationReadFrom_st_core S
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s))
      (Protocol.proposal_time S.E s)
  have hFJ : Block.preceq (proposerReadAt S rho s).st.core.F
      (proposerReadAt S rho s).st.core.J = true := by
    rw [hcore]
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.proposal_time S.E s) (S.E.proposer s))
  have hroot := StoreFinality.finalized_preceq_fgRoot (st := (proposerReadAt S rho s).st.core) hFJ
  show Block.Preceq _ (Protocol.with_proposal_input
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st.core.toHealing id).parent
  rw [Proofs.ModelProperties.with_proposal_input_id_parent]
  exact Proofs.ModelProperties.Preceq_trans hroot
    (Proofs.ModelProperties.Preceq_trans
      (Proofs.ModelProperties.fg_root_Preceq_get_sg_root_with_gradeContract
        (proposerReadAt S rho s).cache S.E S.hc
        (proposerReadAt S rho s).st.core.toHealing
        (S.hc.round_of (proposerReadAt S rho s).st.core.toHealing.s))
      (get_sg_root_with_preceq_get_head_with
        (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc
        (proposerReadAt S rho s).st.core.toHealing _ _ _))


/-- Every row the named selector offers has round at most the round of the store's slot. -/
theorem selected_row_round_le (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    {a : NamedAttestation V}
    (ha : a ∈ Protocol.NamedProposalRows.select .poolAndCarried hc st) :
    a.round ≤ hc.round_of st.core.s := by
  rw [NamedProposalRows.selected_source_exact] at ha
  have hw : Protocol.ProposalRows.inWindow hc st.core a.round = true := by
    rcases List.mem_append.mp ha with hp | hcarr
    · exact (List.mem_filter.mp hp).2
    · obtain ⟨B, -, hrow⟩ := List.mem_flatMap.mp hcarr
      by_cases hb : Protocol.NamedProposalRows.eligibleBody hc st B
      · rw [if_pos hb] at hrow
        exact (List.mem_filter.mp hrow).2
      · rw [if_neg hb] at hrow
        exact absurd hrow (List.not_mem_nil)
  have hw' : hc.round_of st.core.s - hc.η_SG ≤ a.round ∧ a.round ≤ hc.round_of st.core.s := by
    simpa only [Protocol.ProposalRows.inWindow, decide_eq_true_eq] using hw
  exact hw'.2

/-- The attestations of the proposal computed at slot `s` pass `carried_attestations_admissible`. -/
theorem proposedBlockErased_carried_admissible (S : Setup V) (rho : Run V) (s : Slot)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    Protocol.carried_attestations_admissible S.hc B.erase = true := by
  have hpay := Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract
    (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  have hslot : B.erase.slot = (proposerReadAt S rho s).st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hpay.2.2.1]
    show (Protocol.with_proposal_input
        (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc
        (S.node (S.E.proposer s)) (proposerReadAt S rho s).st.core.toHealing id).slot = _
    rw [Proofs.ModelProperties.with_proposal_input_id_slot, Proofs.ModelProperties.toHealing_s]
  rw [Proofs.ModelProperties.carried_attestations_admissible_eq_true_iff, hslot,
    Proofs.NamedWire.erase_attestations]
  intro a ha
  obtain ⟨row, hrow, hae⟩ := List.mem_map.mp ha
  rw [hpay.2.2.2.2.2.2.1] at hrow
  have hsel := NamedProposalRows.mem_proposalRows B.parent _ row hrow
  have := selected_row_round_le S.hc (proposerReadAt S rho s).st hsel.1
  rw [← hae, Proofs.ModelProperties.erase_round]
  exact this


/-- When the erasure of `B` meets every check of the checked core handler, the handler inserts it
    into the tree. -/
theorem erased_handler_inserts (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hparentTree : B.erase.parent ∈ st.core.T) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s) (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried : Protocol.carried_attestations_admissible S.hc B.erase = true) :
    B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase).T := by
  have hfirst : ¬ (st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
      B.erase.parent ∉ st.core.T) := by
    simp only [not_or]
    exact ⟨Nat.not_lt.mpr hslot, hfresh, not_not.mpr hparentTree⟩
  have hfinal : (!Block.preceq st.core.F B.erase) = false := by rw [hF]; rfl
  simp [Protocol.on_block_checked_using, hcarried,
    Protocol.on_block_using, hfirst, hfinal, hproposer, hparent,
    Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T S.E]


/-! ## The proposal is retained by its proposer -/

/-- For `s > 0`, the erasure of the proposal computed at slot `s` is not in the tree of the
    proposer's read. -/
theorem proposedBlockErased_fresh_at_tick (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (s : Slot) (hs : 0 < s)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    B.erase ∉ (proposerReadAt S rho s).st.core.T := by
  intro hmem
  have hlt := Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal
    S adm hs (le_refl (Protocol.proposal_time S.E s)) hmem
  rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hB] at hlt
  exact Nat.lt_irrefl s hlt

#print axioms proposedBlockErased_fresh_at_tick

/-- The erased parent of the proposal is the selected parent `proposedParent S rho s`. -/
theorem proposedBlockErased_parent (S : Setup V) (rho : Run V) (s : Slot)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    B.erase.parent = proposedParent S rho s := by
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho s hB
  rw [Proofs.NamedWire.erase_parent]
  cases B with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node q _ _ _ _ _ _ =>
    simp only [NamedBlock.parent?, Option.some.injEq] at hp
    subst hp
    rw [Proofs.ModelProperties.named_parent_node]
    exact hpe

/-- For `s > 0`, the proposer's block handler retains the proposal computed at slot `s` as a named
    body. -/
theorem proposedBlockAt_admit (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (s : Slot) (hs : 0 < s) {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies := by
  have hpay := Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract
    (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  have hstore : B.erase.slot = (proposerReadAt S rho s).st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hpay.2.2.1]; rfl
  have hsslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]; exact proposedBlockAt_slot S rho s hB
  have hpar : B.erase.parent = proposedParent S rho s :=
    proposedBlockErased_parent S rho s hB
  have hfresh := proposedBlockErased_fresh_at_tick S adm s hs hB
  have hparentTree : B.erase.parent ∈ (proposerReadAt S rho s).st.core.T := by
    rw [hpar]; exact proposedParent_mem S rho s
  have hparent : B.erase.parent.slot < B.erase.slot := by
    rw [hsslot, hpar]
    exact Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal S adm hs
      (le_refl (Protocol.proposal_time S.E s)) (proposedParent_mem S rho s)
  have hparentPreceq : Block.Preceq B.erase.parent B.erase := by
    cases B with
    | genesis => exact Block.preceq_self _
    | node q sl r gv sup rows pr =>
      exact Protocol.preceq_of_parent?
        (show (NamedBlock.node q sl r gv sup rows pr : NamedBlock V).erase.parent? =
          some (NamedBlock.node q sl r gv sup rows pr : NamedBlock V).erase.parent from rfl)
  have hF : Block.Preceq (proposerReadAt S rho s).st.core.F B.erase :=
    Block.preceq_trans (hpar ▸ finalized_preceq_proposedParent S rho s) hparentPreceq
  have hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot) := by
    rw [Proofs.NamedWire.erase_proposer, hsslot]
    exact proposedBlockAt_proposer S rho s hB
  exact proposedBlockAt_on_block_with_bodies S rho s hB hfresh
    (erased_handler_inserts S (proposerReadAt S rho s).st B hparentTree hfresh
      (le_of_eq hstore) hF hproposer hparent
      (proposedBlockErased_carried_admissible S rho s hB))


#print axioms fg_root_preceq_get_sg_root_with_frame
#print axioms get_sg_root_with_preceq_get_head_with
#print axioms finalized_preceq_proposedParent
#print axioms proposedBlockErased_carried_admissible
#print axioms proposedBlockAt_admit

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
