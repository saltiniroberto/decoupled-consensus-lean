import Model.Conditions.Sts_Conditions

/-!
# The execution hypotheses of the explicit end results

The constraints on an execution that each explicit end result `EndResults.…_holds_explicit` takes
as its one hypothesis `admittedExecution`, each named. Five are defined here, stated over a model
`M : Record.Model V`; `HonestRootsNew` and `TimeDiverges` are in
`Model.Conditions.Sts_Conditions`. The six other than `TimeDiverges` are the fields of
`ExecutionValid`, one each.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every payload in the sent log `x[i].sent` whose author is honest through the time `x[i].time`
    (`HonestThrough`) is also in `x[i].sent` signed by that author. -/
def SignaturesUnforgeable (M : Record.Model V) {S : Setup V} (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ (i : Nat) (sm : SignedMsg V (NamedObject V)) (u : V),
    sm ∈ x[i].sent → NamedObject.author sm.msg = some u →
    HonestThrough M Sched x i u →
    (⟨u, sm.msg⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent

/-- Every Goldfish vote or attestation included in a block of the sent log `x[i].sent` (`carries`),
    whose author is honest through the time `x[i].time` (`HonestThrough`), is in `x[i].sent`
    signed by that author. -/
def IncludedSignaturesUnforgeable (M : Record.Model V) {S : Setup V} (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ (i : Nat) (sm : SignedMsg V (NamedObject V)) (o' : NamedObject V) (u : V),
    sm ∈ x[i].sent → carries sm.msg o' → NamedObject.author o' = some u →
    HonestThrough M Sched x i u →
    (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent

/-- A block delivered at a step has every vote of `gf_votes` from the slot before the block's and
    by a member of that slot's committee, and every vote of `gf_support_votes` in `gf_votes`; a
    Goldfish vote delivered at a step is by a member of its slot's committee. -/
def DeliveredMessagesWellFormed (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    x.lbl j = AtomicAction.deliver w sm →
    (∀ B : NamedBlock V, sm.msg = NamedObject.block B →
      (∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) ∧
        (∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) ∧
        (∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot)) ∧
    (∀ u : GoldfishVote V, sm.msg = NamedObject.gfVote u → u.val_index ∈ S.E.committee u.slot)

/-- A block delivered to a validator `w` at step `j` has its parent among the bodies of `w`'s store
    in the configuration `x[j]`. -/
def DeliveredBlocksHaveParent (M : Record.Model V) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    x.lbl j = AtomicAction.deliver w sm →
    ∀ B : NamedBlock V, sm.msg = NamedObject.block B → B.parent ∈ (x[j][w].st).st.bodies

/-- For any two blocks `B` and `C` that satisfy `blockInLog`, two blocks with the same root, each an
    ancestor of `B` or of `C`, are equal. -/
def BlockRootsCollisionFree (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ B C : NamedBlock V,
    blockInLog M S Sched x B →
    blockInLog M S Sched x C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D


/-- The constraints on the execution `x` itself, one conjunct each:
    - `SignaturesUnforgeable`: a payload in the sent log, by an author honest so far, is in it
      signed by that author;
    - `IncludedSignaturesUnforgeable`: a vote or attestation in a sent block, by an author honest
      so far, is sent signed by that author;
    - `DeliveredMessagesWellFormed`: a delivered block's votes are of the slot before it and by
      that slot's committee, and a delivered vote is by its slot's committee;
    - `DeliveredBlocksHaveParent`: a delivered block's parent is already in the receiving
      validator's store;
    - `BlockRootsCollisionFree`: of the ancestors of two blocks with `blockInLog`, two with the
      same root are equal;
    - `HonestRootsNew`: at its slot's proposal time, an honest proposer holds no block with that
      slot's `new_root`;
    - `TimeDiverges`: every natural number is at most the time `x[i].time` of some step `i`. -/
def admittedExecution (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  SignaturesUnforgeable M Sched x ∧ IncludedSignaturesUnforgeable M Sched x ∧
    DeliveredMessagesWellFormed M S x ∧ DeliveredBlocksHaveParent M x ∧
    BlockRootsCollisionFree M S Sched x ∧ HonestRootsNew M S Sched x ∧ TimeDiverges M x

end

end DecoupledConsensusModel.Sts.Restated
