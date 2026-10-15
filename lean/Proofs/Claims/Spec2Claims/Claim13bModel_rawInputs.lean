module

public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.rawInputs`

Lemmas that unfold the attestations of one sender a round's grade reads at a cutoff: those held in
the pool of a round of the expiry window `Protocol.latest_window`, signed by that sender, and
stamped strictly before the cutoff. They also unfold the stamp test `occurrenceBefore`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.rawInputs
  DecoupledConsensusModel.occurrenceBefore

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the grade view `gv` holds the attestation `u` in its pool of round `k`, `k` is in
    `latest_window eta r`, `u` is signed by `sender`, and `gv` stamps `u` strictly before `cutoff`,
    then `u` is among `sender`'s raw inputs to the round-`r` grade at that cutoff. -/
theorem mem_rawInputs_of_stamp (gv : Protocol.GradeView V) (eta r k : Round) (cutoff : Time)
    (sender : V) {u : Protocol.SGVote V} (hk : k ∈ Protocol.latest_window eta r)
    (hu : u ∈ gv.sg_votes k) (hidx : u.val_index = sender) {stamp : Time}
    (hts : gv.timestamp_sg_vote u = some (stamp : Stamp)) (hlt : stamp < cutoff) :
    u ∈ Protocol.rawInputs gv eta r cutoff sender := by
  unfold Protocol.rawInputs
  refine Finset.mem_filter.mpr ⟨?_, hidx, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨k, List.mem_toFinset.mpr hk, hu⟩
  · unfold occurrenceBefore
    rw [hts]
    exact decide_eq_true (WithBot.coe_lt_coe.mpr hlt)

omit [Fintype V] in
/-- Every attestation among `sender`'s raw inputs to a grade is signed by `sender`. -/
theorem val_index_of_mem_rawInputs {gv : Protocol.GradeView V} {eta r : Round} {cutoff : Time}
    {sender : V} {u : Protocol.SGVote V} (hu : u ∈ Protocol.rawInputs gv eta r cutoff sender) :
    u.val_index = sender := by
  unfold Protocol.rawInputs at hu
  exact (Finset.mem_filter.mp hu).2.1

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the grade view `gv` holds the attestation `u` in its pool of round `k`, `k` is in
    `latest_window eta r`, `u` is signed by `sender`, and the stamp `gv` gives `u` occurs before
    `cutoff`, then `u` is among `sender`'s raw inputs to the round-`r` grade at that cutoff. -/
theorem mem_rawInputs_of_occurrenceBefore (gv : Protocol.GradeView V) (eta r k : Round)
    (cutoff : Time) (sender : V) {u : Protocol.SGVote V} (hk : k ∈ Protocol.latest_window eta r)
    (hu : u ∈ gv.sg_votes k) (hidx : u.val_index = sender)
    (hocc : occurrenceBefore (gv.timestamp_sg_vote u) cutoff = true) :
    u ∈ Protocol.rawInputs gv eta r cutoff sender := by
  unfold Protocol.rawInputs
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, List.mem_toFinset.mpr hk, hu⟩, hidx, hocc⟩

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `u` is among `sender`'s raw inputs in the grade view `gv`, for the window `eta` before round
    `r` and the cutoff `cutoff`, then `u` is among `gv`'s SG votes of some round of that window. -/
theorem mem_sg_votes_of_mem_rawInputs {gv : Protocol.GradeView V} {eta r : Round}
    {cutoff : Time} {sender : V} {u : Protocol.SGVote V}
    (hu : u ∈ Protocol.rawInputs gv eta r cutoff sender) :
    ∃ k ∈ Protocol.latest_window eta r, u ∈ gv.sg_votes k := by
  unfold Protocol.rawInputs at hu
  obtain ⟨hpool, -⟩ := Finset.mem_filter.mp hu
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
  exact ⟨k, List.mem_toFinset.mp hk, huk⟩

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `u` is among `sender`'s raw inputs in the grade view `gv`, for round `r`, the window length
    `eta` and the cutoff `cutoff`, then `u` is an SG vote `gv` holds for some round of
    `latest_window eta r`. -/
theorem exists_window_of_mem_rawInputs {gv : Protocol.GradeView V} {eta r : Round}
    {cutoff : Time} {sender : V} {u : Protocol.SGVote V}
    (hu : u ∈ Protocol.rawInputs gv eta r cutoff sender) :
    ∃ k, k ∈ Protocol.latest_window eta r ∧ u ∈ gv.sg_votes k := by
  unfold Protocol.rawInputs at hu
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hu).1
  exact ⟨k, List.mem_toFinset.mp hk, huk⟩

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- An attestation a round-`r` grade counts for `sender` is held in the pool of a round of
    `latest_window eta r`, is signed by `sender`, and was stamped before the cutoff. -/
theorem rawInputs_mem_window (gv : Protocol.GradeView V) (eta r : Round) (cutoff : Int)
    (sender : V) {u : Protocol.SGVote V}
    (hu : u ∈ Protocol.rawInputs gv eta r cutoff sender) :
    (∃ k ∈ Protocol.latest_window eta r, u ∈ gv.sg_votes k) ∧ u.val_index = sender ∧
      occurrenceBefore (gv.timestamp_sg_vote u) cutoff = true := by
  simp only [Protocol.rawInputs, Finset.mem_filter, Finset.mem_biUnion,
    List.mem_toFinset] at hu
  exact ⟨hu.1, hu.2.1, hu.2.2⟩

end DecoupledConsensusModel.Sts
