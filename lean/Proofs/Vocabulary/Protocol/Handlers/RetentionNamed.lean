module
public import Proofs.Vocabulary.Protocol.Handlers.Monotone
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The named handler chain -/

theorem on_block_using_latest (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [Protocol.update_finality_latest,
          Protocol.foldl_on_goldfish_vote_checked_latest]

omit [DecidableEq V] [Fintype V] in
theorem on_block_checked_using_latest (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : (handle st).latest_confirmed = st.latest_confirmed) :
    (Protocol.on_block_checked_using handle hc st B).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · rfl

omit [Fintype V] in
private theorem commitBlock_latest (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).latest_confirmed = after.latest_confirmed := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

theorem process_block_core_latest (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  all_goals first
    | rfl
    | (rw [commitBlock_latest]
       exact on_block_checked_using_latest _ hc st.core B.erase
         (on_block_using_latest E st.core B.erase _))

omit [Fintype V] in
theorem admit_row_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact Protocol.on_sg_vote_latest hc st.core row.erase

omit [Fintype V] in
private theorem foldl_admit_row_latest (hc : HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).latest_confirmed =
      st.latest_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_latest]

omit [Fintype V] in
theorem admit_rows_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).latest_confirmed = st.latest_confirmed :=
  foldl_admit_row_latest hc rows st

omit [Fintype V] in
theorem admit_carried_latest (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).latest_confirmed =
      after.latest_confirmed := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_latest hc after B.attestations
      · rfl

theorem on_block_with_latest (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_latest]
  exact process_block_core_latest E hc cfg st B


/-- Processing an object leaves `latest_confirmed` unchanged. -/
theorem node_process_latest (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (NamedNode.process S n o).st.core.latest_confirmed = n.st.core.latest_confirmed := by
  cases o with
  | block B => exact on_block_with_latest .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u => exact Protocol.on_goldfish_vote_checked_latest S.E n.st.core u
  | attest a => exact admit_row_latest S.hc n.st a


/-! ## Along the run -/


omit [Fintype V] in
theorem update_finality_stable (st : Protocol.Store V) (sigma : ChainState V) :
    (Protocol.update_finality st sigma).latest_stable = st.latest_stable := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
theorem on_goldfish_vote_stable (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).latest_stable = st.latest_stable := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

theorem on_goldfish_vote_checked_stable (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).latest_stable = st.latest_stable := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_stable st u
  · rfl

theorem foldl_on_goldfish_vote_checked_stable (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).latest_stable = st.latest_stable := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih => rw [List.foldl_cons, ih, on_goldfish_vote_checked_stable]

omit [Fintype V] in
theorem on_sg_vote_stable (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).latest_stable = st.latest_stable := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

theorem on_block_using_stable (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).latest_stable = st.latest_stable := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_stable, foldl_on_goldfish_vote_checked_stable]

omit [DecidableEq V] [Fintype V] in
theorem on_block_checked_using_stable (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : (handle st).latest_stable = st.latest_stable) :
    (Protocol.on_block_checked_using handle hc st B).latest_stable = st.latest_stable := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · rfl

omit [Fintype V] in
private theorem commitBlock_stable (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).core.latest_stable =
      after.latest_stable := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

theorem process_block_core_stable (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  all_goals first
    | rfl
    | (rw [commitBlock_stable]
       exact on_block_checked_using_stable _ hc st.core B.erase
         (on_block_using_stable E st.core B.erase _))

omit [Fintype V] in
theorem admit_row_stable (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact on_sg_vote_stable hc st.core row.erase

omit [Fintype V] in
private theorem foldl_admit_row_stable (hc : HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).core.latest_stable =
      st.core.latest_stable := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_stable]

omit [Fintype V] in
theorem admit_rows_stable (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.latest_stable =
      st.core.latest_stable :=
  foldl_admit_row_stable hc rows st

omit [Fintype V] in
theorem admit_carried_stable (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).core.latest_stable =
      after.core.latest_stable := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_stable hc after B.attestations
      · rfl

theorem on_block_with_stable (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_stable]
  exact process_block_core_stable E hc cfg st B

theorem propose_block_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedDuties.propose_block_with]
  cases Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => rfl
  | some B => exact on_block_with_stable .alsoCarried E hc cfg st B

theorem goldfish_vote_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1.latest_stable =
      st.latest_stable := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_stable E st _
  · rfl

theorem named_goldfish_vote_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedDuties.goldfish_vote_with]
  exact goldfish_vote_with_stable contract E hc nd st.core

theorem attest_with_stable (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core.latest_stable =
      st.core.latest_stable := by
  simp only [Protocol.NamedDuties.attest_with]
  exact admit_row_stable hc st _

/-- Processing an object leaves `latest_stable` unchanged. -/
theorem node_process_stable (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (NamedNode.process S n o).st.core.latest_stable = n.st.core.latest_stable := by
  cases o with
  | block B => exact on_block_with_stable .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u => exact on_goldfish_vote_checked_stable S.E n.st.core u
  | attest a => exact admit_row_stable S.hc n.st a

#print axioms process_block_core_stable
#print axioms propose_block_with_stable
#print axioms named_goldfish_vote_with_stable
#print axioms attest_with_stable
#print axioms node_process_stable

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
