module
public import Proofs.Vocabulary.Internal.Definitions.PhaseGrades
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ActionSources
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedAdmissible
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ProposalSourcesInternal
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Blocks

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Shared premises -/


/-- The validators of `Hon` with an interpreted input by `cutoff` at this reader. -/
def honestPresent (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) : Finset V :=
  Hon.filter fun v =>
    (DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v).Nonempty

/-- The faulty weight is less than the weight of the honest validators present at `cutoff`. -/
def WindowMajorityAt (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) : Prop :=
  E.electorate.weightOf (Finset.univ \ Hon) <
    E.electorate.weightOf (honestPresent hc gv F Hon r cutoff)


/-- For every validator of `Hon`, the head of its latest interpreted input by `cutoff`, when in the
    reader's tree, is an ancestor of `Can`. -/
def BatchAlignedAt (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) (Can : Block V) : Prop :=
  ∀ v ∈ Hon, ∀ u ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v,
    (∀ u' ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v, u'.round ≤ u.round) →
    ∀ head, u.confirmed = some head.root → Block.find? gv.T head.root = some head →
      Block.Preceq head Can

/-- The G0 late cutoff of round `r`, the earliest of the phase cutoffs, so presence by it implies
    presence by every phase cutoff. -/
abbrev allPhasesCutoff (E : Env V) (hc : Protocol.HealConfig) (r : Round) : Time :=
  late E hc r .g0

/-- `v`'s node state made of every event strictly before `t`. -/
abbrev readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) : NamedNodeState V :=
  NamedRun.stateBeforeTime S rho t v

abbrev filteredTree (n : NamedNodeState V) : Finset (Block V) :=
  Protocol.get_filtered_block_tree n.st.core.toHealing.toFG


/-! ## Selector facts at a node -/


/-- The SG block of every action is one of four: a clear descendant of the anchor that is an
    ancestor of `live_confirmed`; the active G2 candidate; the FG root when raw G2 exists but no
    active candidate; or the anchor. -/
def Q31_actionSGBlock_tiers (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (r : Round),
    let n := actionReadAt S rho v r
    let A := nodeAnchor S n r
    (Block.Preceq A (actionSGBlockAt S rho v r) ∧
      Block.Preceq (actionSGBlockAt S rho v r) n.st.core.live_confirmed ∧
      nodeClear S n r (actionSGBlockAt S rho v r) = true) ∨
    (∃ Q, nodeQ2 S n r = some Q ∧ actionSGBlockAt S rho v r = Q) ∨
    (nodeQ2 S n r = none ∧ nodeRawG2 S n r ∧
      actionSGBlockAt S rho v r = Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
    (nodeQ2 S n r = none ∧ ¬ nodeRawG2 S n r ∧ actionSGBlockAt S rho v r = A)


end DecoupledConsensusModel.Internal.PhaseGrades

end
