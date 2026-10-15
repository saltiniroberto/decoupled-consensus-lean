module
public import Proofs.Vocabulary.Protocol.Grades.FrameCompleted
public import Proofs.Vocabulary.Protocol.Grades.RowTrace
public import Proofs.Vocabulary.Protocol.Store.PublicCutSG
public import Proofs.Vocabulary.Protocol.Handlers.PublicCutBody
public import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
public import Proofs.Vocabulary.Protocol.Grades.Grades
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The grade-2 block precedes the anchor

An honest node freezes its round-`r` G2 root at `opening r - Δ` and its G1 root at `opening r`. This
file relates the node's reads at those two times, carries gradedness from the G2 domain time to the
G1 domain time, and proves that the frame's grade-2 block precedes the frame's anchor.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Token algebra -/

/-- Support for `B` transports from one token view to another when every early token of the first
    view that covers `B` is an early token of the second. -/
theorem q10_supports_transport {Key Blk : Type*} (c₁ c₂ : Key → Blk → Prop)
    {ea eb la lb rawa rawb : Finset (Token Key)} {B : Blk}
    (hkeep : ∀ u ∈ ea, c₁ u.key B → u ∈ eb)
    (heb_la : eb ⊆ la) (hlb_la : lb ⊆ la) (hrawb : rawb ⊆ rawa)
    (hea_rawa : ea ⊆ rawa) (heb_rawa : eb ⊆ rawa)
    (hc : ∀ k, c₁ k B → c₂ k B)
    (hS : Supports c₁ ea la rawa B) : Supports c₂ eb lb rawb B := by
  obtain ⟨u, hu, _hmax, hcov, hclean, hsweep⟩ := hS
  have hub : u ∈ eb := hkeep u hu hcov
  obtain ⟨u', hu', hmax'⟩ := Finset.exists_max_image eb (fun t => t.round) ⟨u, hub⟩
  have hle : u.round ≤ u'.round := hmax' u hub
  refine ⟨u', hu', hmax', ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact hc _ (hsweep u' (heb_la hu') hlt)
    · have hkey : u'.key = u.key :=
        hclean u' (heb_rawa hu') u (hea_rawa hu) hle heq.symm
      rw [hkey]
      exact hc _ hcov
  · intro x hx y hy hkx hxy
    exact hclean x (hrawb hx) y (hrawb hy) (le_trans hle hkx) hxy
  · intro x hx hlt
    exact hc _ (hsweep x (hlb_la hx) (lt_of_le_of_lt hle hlt))

/-- Opposition to `B` transports to a token view whose early set is contained in the first view's
    and whose late and raw sets contain the first view's. -/
theorem q10_opposes_transport {Key Blk : Type*} (c₁ c₂ : Key → Blk → Prop)
    {ea eb la lb rawa rawb : Finset (Token Key)} {B : Blk}
    (he : ea ⊆ eb) (hl : lb ⊆ la) (hraw : rawb ⊆ rawa)
    (hc : ∀ k, c₂ k B → c₁ k B)
    (hO : Opposes c₁ eb lb rawb B) : Opposes c₂ ea la rawa B := by
  rcases hO with ⟨x, hx, hguard, hnot⟩ | ⟨x, hx, y, hy, hguard, hround, hkey⟩
  · exact Or.inl ⟨x, hl hx, fun u hu => hguard u (he hu), fun hcov => hnot (hc _ hcov)⟩
  · exact Or.inr ⟨x, hraw hx, y, hraw hy, fun u hu => hguard u (he hu), hround, hkey⟩

/-- A token view whose early set is non-empty and contained in its late set, and which does not
    oppose `B`, supports `B`. -/
theorem q10_supports_of_not_opposes {Key Blk : Type*} (c : Key → Blk → Prop)
    {e l raw : Finset (Token Key)} {B : Blk}
    (hel : e ⊆ l) (hne : e.Nonempty) (hO : ¬ Opposes c e l raw B) :
    Supports c e l raw B := by
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image e (fun t => t.round) hne
  refine ⟨u, hu, hmax, ?_, ?_, ?_⟩
  · by_contra hcov
    exact hO (Or.inl ⟨u, hel hu, hmax, hcov⟩)
  · intro x hx y hy hux hxy
    by_contra hkey
    exact hO (Or.inr ⟨x, hx, y, hy, fun w hw => le_trans (hmax w hw) hux, hxy, hkey⟩)
  · intro x hx hlt
    by_contra hcov
    exact hO (Or.inl ⟨x, hx, fun w hw => le_of_lt (lt_of_le_of_lt (hmax w hw) hlt), hcov⟩)

/-- A token view that supports `B` does not oppose `B`. -/
theorem q10_not_opposes_of_supports {Key Blk : Type*} (c : Key → Blk → Prop)
    {e l raw : Finset (Token Key)} {B : Blk}
    (hel : e ⊆ l) (hlr : l ⊆ raw)
    (hS : Supports c e l raw B) : ¬ Opposes c e l raw B := by
  obtain ⟨u, hu, _hmax, hcov, hclean, hsweep⟩ := hS
  rintro (⟨x, hx, hguard, hnot⟩ | ⟨x, hx, y, hy, hguard, hround, hkey⟩)
  · rcases Nat.lt_or_ge u.round x.round with hlt | hge
    · exact hnot (hsweep x hx hlt)
    · have heq : u.round = x.round := Nat.le_antisymm (hguard u hu) hge
      have hk : u.key = x.key := hclean u (hlr (hel hu)) x (hlr hx) le_rfl heq
      exact hnot (hk ▸ hcov)
  · exact hkey (hclean x hx y hy (hguard u hu) hround)

/-! ## Cutoff monotonicity inside one store -/

omit [Fintype V] in
/-- The raw inputs of a sender grow with the cutoff. -/
theorem q10_rawInputs_cut (gv : Protocol.GradeView V) (eta r : Round) {c d : Time}
    (hcd : c ≤ d) (sender : V) :
    DecoupledConsensusModel.Protocol.rawInputs gv eta r c sender ⊆
      DecoupledConsensusModel.Protocol.rawInputs gv eta r d sender := by
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.1, occurrenceBefore_mono hcd hu.2.2⟩

omit [Fintype V] in
/-- A body ready by cutoff `c` is ready by every later cutoff `d`. -/
theorem q10_bodyReady_cut (gv : Protocol.GradeView V) (F : Block V) {c d : Time}
    (hcd : c ≤ d) (u : Protocol.SGVote V)
    (h : DecoupledConsensusModel.Protocol.bodyReady gv F c u = true) :
    DecoupledConsensusModel.Protocol.bodyReady gv F d u = true := by
  cases hconf : u.confirmed with
  | none => simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
  | some root =>
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at h ⊢
    cases hf : Block.find? gv.T root with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some H =>
      rw [hf] at h
      simp only [Bool.and_eq_true] at h ⊢
      refine ⟨?_, h.2⟩
      rw [stampedBefore_eq_occurrenceBefore] at h ⊢
      exact occurrenceBefore_mono hcd h.1

omit [Fintype V] in
/-- The interpreted inputs of a sender grow with the cutoff. -/
theorem q10_interpreted_cut (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (sender : V) :
    DecoupledConsensusModel.Protocol.interpretedInputs gv F eta r c sender ⊆
      DecoupledConsensusModel.Protocol.interpretedInputs gv F eta r d sender := by
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.interpretedInputs, Finset.mem_filter] at hu ⊢
  exact ⟨q10_rawInputs_cut gv eta r hcd sender hu.1, q10_bodyReady_cut gv F hcd u hu.2⟩

omit [Fintype V] in
theorem q10_readyView_cut (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (v : V) :
    readyView gv F eta r c v ⊆ readyView gv F eta r d v :=
  Finset.image_subset_image (q10_interpreted_cut gv F eta r hcd v)

omit [Fintype V] in
theorem q10_rawView_cut (gv : Protocol.GradeView V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (v : V) :
    rawView gv eta r c v ⊆ rawView gv eta r d v :=
  Finset.image_subset_image (q10_rawInputs_cut gv eta r hcd v)

omit [Fintype V] in
theorem q10_ready_subset_raw (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (c : Time) (v : V) :
    readyView gv F eta r c v ⊆ rawView gv eta r c v :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-! ## The phase windows -/

theorem q10_early_g2_le_early_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ early S.E S.hc r .g1 := by
  change opening S.E S.hc r + (-5) * S.E.Δ ≤ opening S.E S.hc r + (-4) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) S.E.Δ_pos.le) _

theorem q10_early_g1_le_domain_g2 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 ≤ domain S.E S.hc r .g2 := by
  change opening S.E S.hc r + (-4) * S.E.Δ ≤ opening S.E S.hc r + (-1) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) S.E.Δ_pos.le) _

theorem q10_late_g1_le_domain_g2 (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 ≤ domain S.E S.hc r .g2 := by
  change opening S.E S.hc r + (-2) * S.E.Δ ≤ opening S.E S.hc r + (-1) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) S.E.Δ_pos.le) _

theorem q10_late_g2_eq_domain_g2 (S : Setup V) (r : Round) :
    late S.E S.hc r .g2 = domain S.E S.hc r .g2 := rfl

theorem q10_early_le_late (S : Setup V) (r : Round) (p : Phase) :
    early S.E S.hc r p ≤ late S.E S.hc r p := by
  cases p <;>
    simp only [early, late, Phase.earlyOffset, Phase.lateOffset] <;>
    exact Int.add_le_add_left
      (Int.mul_le_mul_of_nonneg_right (by decide) S.E.Δ_pos.le) _

theorem q10_domain_g2_lt_domain_g1 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 < domain S.E S.hc r .g1 := by
  change opening S.E S.hc r + (-1) * S.E.Δ < opening S.E S.hc r + 0 * S.E.Δ
  have key : ∀ d : Int, 0 < d → (-1) * d < 0 * d := by intro d h; omega
  exact Int.add_lt_add_left (key S.E.Δ S.E.Δ_pos) _

/-! ## Two reads of one honest node -/

omit [DecidableEq V] [Fintype V] in
/-- An event with a smaller key has an earlier or equal time. -/
private theorem q10_time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

private theorem q10_publicTime_nonneg (S : Setup V) {cut : Time}
    (hpublic : PublicTime S cut) : 0 ≤ cut := by
  obtain ⟨k, rfl⟩ := hpublic
  exact Int.mul_nonneg (by exact_mod_cast Nat.zero_le k) S.E.Δ_pos.le

omit [DecidableEq V] [Fintype V] in
/-- In a key-sorted run, an event with an earlier time has a smaller index. -/
private theorem q10_index_lt_of_time_lt (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i j : Nat} {e f : NamedEvent V}
    (he : rho.events[i]? = some e) (hf : rho.events[j]? = some f)
    (ht : e.time < f.time) : i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases hji.eq_or_lt with rfl | hji
  · have hef : e = f := Option.some.inj (he.symm.trans hf)
    exact (ne_of_lt ht) (congrArg NamedEvent.time hef)
  · obtain ⟨hi, hgeti⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp hf
    have hkey := (List.pairwise_iff_getElem.mp hsorted) j i hj hi hji
    rw [hgetj, hgeti] at hkey
    exact (not_lt_of_ge (q10_time_le_of_key_le hkey)) ht

/-- Past the run's horizon, the read before `cut` is the read after every event. -/
private theorem q10_read_eq_full_of_horizon_lt (S : Setup V)
    (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {cut : Time} (hhorizon : rho.horizon < cut) :
    NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho rho.events.length := by
  unfold NamedRun.stateBeforeTime NamedRun.stateBefore
  rw [List.filter_eq_self.mpr, List.take_length]
  intro e he
  simp only [decide_eq_true_eq]
  exact (sch.in_horizon e he).2.trans_lt hhorizon

/-- A row held at a read whose SG vote stamp is before a public cutoff `cut` was already held at the
    read before `cut`. -/
theorem q10_row_at_public_cut (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {reader : V} {cut read : Time}
    (hpublic : PublicTime S cut) {a : NamedAttestation V}
    (hheld : a ∈ (NamedRun.stateBeforeTime S rho read reader).st.sg_rows a.round)
    (hstamp : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho read reader).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) cut = true) :
    a ∈ (NamedRun.stateBeforeTime S rho cut reader).st.sg_rows a.round := by
  obtain ⟨j, accepted, hearly, hacc⟩ :=
    NamedPublicCutSG.sg_row_accepted_before_public_cut S rho sch hpublic hheld hstamp
  obtain ⟨e, he, hnode, het⟩ := hacc.1.2
  have hpost : a ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  by_cases hhor : cut ≤ rho.horizon
  · have hreader : reader ∈ rho.honest := by
      simpa only [hnode] using sch.honest_only e (List.mem_of_getElem? he)
    have htickMem := sch.tick_total reader hreader cut hpublic
      (q10_publicTime_nonneg S hpublic) hhor
    obtain ⟨k, htick⟩ := List.mem_iff_getElem?.mp htickMem
    have hjk : j < k := q10_index_lt_of_time_lt rho sch.sorted he htick
      (by rw [het]; exact hearly)
    rw [← Proofs.NamedRuntime.tick_prefix_eq_strict S rho sch.sorted sch.nodup htick]
    exact (Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader
      (Nat.succ_le_of_lt hjk) hpost).1
  · have hhorizon : rho.horizon < cut := lt_of_not_ge hhor
    rw [q10_read_eq_full_of_horizon_lt S rho sch hhorizon]
    obtain ⟨hjlen, _⟩ := List.getElem?_eq_some_iff.mp he
    exact (Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader
      (Nat.succ_le_of_lt hjlen) hpost).1

/-- A body held at the read before `c` is held at the read before every later `d`, with the same
    timestamp. -/
theorem q10_strict_body_carry (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {c d : Time} (hcd : c ≤ d)
    {H : NamedBlock V}
    (hH : H ∈ (NamedRun.stateBeforeTime S rho c reader).st.bodies) :
    H ∈ (NamedRun.stateBeforeTime S rho d reader).st.bodies ∧
      (NamedRun.stateBeforeTime S rho d reader).st.core.timestamp_block H.erase =
        (NamedRun.stateBeforeTime S rho c reader).st.core.timestamp_block H.erase := by
  rw [strict_read_eq_index S rho sch.sorted c] at hH
  rw [strict_read_eq_index S rho sch.sorted c, strict_read_eq_index S rho sch.sorted d]
  exact NamedBlockStamp.stateBefore_body_stamp_mono S rho reader
    (strict_lengths_mono rho hcd) hH

/-! ## The two `g1` cutoffs are public times -/

private theorem q10_one_le_slots (S : Setup V) (r : Round) (hr : 0 < r) :
    2 ≤ r * S.hc.R :=
  S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hr)

private theorem q10_nat_four (n : Nat) (h : 2 ≤ n) : 4 ≤ 4 * n := by omega

private theorem q10_nat_two (n : Nat) (h : 2 ≤ n) : 2 ≤ 4 * n := by omega

theorem q10_early_g1_public (S : Setup V) (r : Round) (hr : 0 < r) :
    PublicTime S (early S.E S.hc r .g1) := by
  have hcoef : 4 ≤ 4 * (r * S.hc.R) := q10_nat_four _ (q10_one_le_slots S r hr)
  refine ⟨4 * (r * S.hc.R) - 4, ?_⟩
  unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

theorem q10_late_g1_public (S : Setup V) (r : Round) (hr : 0 < r) :
    PublicTime S (late S.E S.hc r .g1) := by
  have hcoef : 2 ≤ 4 * (r * S.hc.R) := q10_nat_two _ (q10_one_le_slots S r hr)
  refine ⟨4 * (r * S.hc.R) - 2, ?_⟩
  unfold late opening Phase.lateOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

/-! ## View inclusions between the two reads -/

omit [Fintype V] in
/-- A block compatible with `F1` is compatible with every `F2 ⪯ F1`. -/
theorem q10_compatible_back {X F2 F1 : Block V} (hF : Block.Preceq F2 F1)
    (h : Block.compatible X F1 = true) : Block.compatible X F2 = true := by
  have h' : Block.preceq X F1 = true ∨ Block.preceq F1 X = true := by
    simpa only [Block.compatible, Bool.or_eq_true] using h
  rcases h' with hXF | hFX
  · exact Block.compatible_of_preceq_common hXF hF
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hF hFX)

/-- For a public time `c` with `c ≤ T2` and `c ≤ T1`, a raw input with cutoff `c` at `v`'s read
    before `T1` is a raw input with cutoff `c` at `v`'s read before `T2`. -/
theorem q10_rawInputs_back (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (v : V) {c T2 T1 : Time}
    (hpublic : PublicTime S c) (hc2 : c ≤ T2) (hc1 : c ≤ T1) (eta r : Round) (sender : V) :
    DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView eta r c sender ⊆
      DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView eta r c sender := by
  intro u hu
  obtain ⟨hpool, hval, hstamp⟩ := Finset.mem_filter.mp hu
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := pool_token_row S rho sch T1 v huk
  subst hproj
  have hstamp1 : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho T1 v).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) c = true := hstamp
  have hatc : a ∈ (NamedRun.stateBeforeTime S rho c v).st.sg_rows a.round :=
    q10_row_at_public_cut S rho sch hpublic hmem hstamp1
  obtain ⟨_, hstampcut⟩ := strict_sg_row_carry S rho sch v hc1 hatc
  have hstampc : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho c v).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) c = true := by
    rw [← hstampcut]
    exact hstamp1
  obtain ⟨hmem2, hstamp2⟩ := strict_sg_row_carry S rho sch v hc2 hatc
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T2 v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T2 v).1.1.1
  have hpool2 := NamedAdmission.pool_view_mem
    (NamedRun.stateBeforeTime S rho T2 v).st hcoh.2.2.2.1 a hmem2
  refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨k, hk, ?_⟩, hval, ?_⟩
  · exact hround ▸ Finset.mem_image_of_mem Protocol.sgVote hpool2
  · show occurrenceBefore
      ((NamedRun.stateBeforeTime S rho T2 v).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) c = true
    rw [hstamp2]
    exact hstampc

/-- For an honest `v`, `T2 ≤ T1` and a public time `c ≤ T2`, an interpreted input with cutoff `c` at
    `v`'s read before `T1` is an interpreted input with cutoff `c` at `v`'s read before `T2`. -/
theorem q10_interpreted_back (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest) {c T2 T1 : Time}
    (hpublic : PublicTime S c) (hc2 : c ≤ T2) (h21 : T2 ≤ T1) (eta r : Round) (sender : V) :
    DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho T1 v).st.core.F eta r c sender ⊆
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho T2 v).st.core.F eta r c sender := by
  have sch := core.toNamedScheduleWellFormed
  have hc1 : c ≤ T1 := hc2.trans h21
  have hFmono : Block.Preceq (NamedRun.stateBeforeTime S rho T2 v).st.core.F
      (NamedRun.stateBeforeTime S rho T1 v).st.core.F := by
    rw [strict_read_eq_index S rho sch.sorted T2, strict_read_eq_index S rho sch.sorted T1]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v (strict_lengths_mono rho h21)
  intro u hu
  obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
  refine Finset.mem_filter.mpr
    ⟨q10_rawInputs_back S rho sch v hpublic hc2 hc1 eta r sender hraw, ?_⟩
  cases hconf : u.confirmed with
  | none => simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
  | some root =>
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
    cases hf : Block.find?
        (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView.T root with
    | none => rw [hf] at hready; exact absurd hready (by simp)
    | some H =>
      rw [hf, Bool.and_eq_true] at hready
      have hroot : H.root = root := Proofs.HealingLemmas.find?_root hf
      have hcoh1 : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T1 v).st :=
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T1 v).1.1.1
      have hHmem : H ∈ (NamedRun.stateBeforeTime S rho T1 v).st.core.T :=
        Proofs.HealingLemmas.find?_mem hf
      rw [hcoh1.1] at hHmem
      obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
      have hstampN : stampedBefore
          (NamedRun.stateBeforeTime S rho T1 v).st.core.timestamp_block c Hn.erase = true := by
        simpa only [hHe, Protocol.Store.toHealing, Protocol.HealingStore.gradeView] using hready.1
      have hcutN : Hn ∈ (NamedRun.stateBeforeTime S rho c v).st.bodies :=
        NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
          S rho sch hpublic hHn hstampN
      obtain ⟨hHn2, hstamp2⟩ := q10_strict_body_carry S rho sch v hc2 hcutN
      obtain ⟨_, hstamp1⟩ := q10_strict_body_carry S rho sch v hc1 hcutN
      have hfind2 : Block.find?
          (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView.T root =
          some H := by
        have := held_find_at_strict S rho sch core.toNamedRootCollisionFree v hv T2 Hn hHn2
        rw [hHe] at this
        rw [← hroot]
        exact this
      rw [hfind2, Bool.and_eq_true]
      refine ⟨?_, q10_compatible_back hFmono hready.2⟩
      have : stampedBefore
          (NamedRun.stateBeforeTime S rho T2 v).st.core.timestamp_block c Hn.erase = true := by
        rw [stampedBefore_eq_occurrenceBefore] at hstampN ⊢
        rw [hstamp2, ← hstamp1]
        exact hstampN
      simpa only [hHe, Protocol.Store.toHealing, Protocol.HealingStore.gradeView] using this

/-! ## Forward transport of a covering input -/

/-- For an honest `v` and `T2 ≤ T1`, a root that resolves to `H` in `v`'s tree before `T2` resolves
    to `H` in `v`'s tree before `T1`. -/
theorem q10_find_fwd (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) (hv : v ∈ rho.honest) {T2 T1 : Time} (h21 : T2 ≤ T1) {root : BlockId}
    {H : Block V}
    (hf : Block.find? (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView.T
      root = some H) :
    Block.find? (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView.T
      root = some H := by
  have sch := core.toNamedScheduleWellFormed
  have hroot : H.root = root := Proofs.HealingLemmas.find?_root hf
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T2 v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T2 v).1.1.1
  have hHmem : H ∈ (NamedRun.stateBeforeTime S rho T2 v).st.core.T :=
    Proofs.HealingLemmas.find?_mem hf
  rw [hcoh.1] at hHmem
  obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
  have hHn1 : Hn ∈ (NamedRun.stateBeforeTime S rho T1 v).st.bodies :=
    (q10_strict_body_carry S rho sch v h21 hHn).1
  have hfind := held_find_at_strict S rho sch core.toNamedRootCollisionFree v hv T1 Hn hHn1
  rw [hHe] at hfind
  rw [← hroot]
  exact hfind

/-- For an honest `v` and `T2 ≤ T1`, a key that covers `B` in `v`'s tree before `T2` covers `B` in
    `v`'s tree before `T1`. -/
theorem q10_localCovers_fwd (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest) {T2 T1 : Time}
    (h21 : T2 ≤ T1) (k : Option BlockId) (B : Block V)
    (h : localCovers (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView k B
      = true) :
    localCovers (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView k B
      = true := by
  cases k with
  | none =>
    simp only [localCovers, Protocol.head_covers] at h
    exact absurd h (by simp)
  | some root =>
    simp only [localCovers, Protocol.head_covers] at h ⊢
    cases hf : Block.find?
        (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView.T root with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some H =>
      rw [hf] at h
      rw [q10_find_fwd S rho core v hv h21 hf]
      exact h

/-- For `T2 ≤ T1` and `c2 ≤ c1`, a raw input with cutoff `c2` at `v`'s read before `T2` is a raw
    input with cutoff `c1` at `v`'s read before `T1`. -/
theorem q10_rawInputs_fwd (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (v : V) {T2 T1 : Time} (h21 : T2 ≤ T1)
    {c1 c2 : Time} (hc : c2 ≤ c1) (eta r : Round) (sender : V) :
    DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView eta r c2 sender ⊆
      DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView eta r c1 sender := by
  intro u hu
  obtain ⟨hpool, hval, hstamp⟩ := Finset.mem_filter.mp hu
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := pool_token_row S rho sch T2 v huk
  subst hproj
  obtain ⟨hmem1, hstamp1⟩ := strict_sg_row_carry S rho sch v h21 hmem
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T1 v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T1 v).1.1.1
  have hpool1 := NamedAdmission.pool_view_mem
    (NamedRun.stateBeforeTime S rho T1 v).st hcoh.2.2.2.1 a hmem1
  refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨k, hk, ?_⟩, hval, ?_⟩
  · exact hround ▸ Finset.mem_image_of_mem Protocol.sgVote hpool1
  · show occurrenceBefore
      ((NamedRun.stateBeforeTime S rho T1 v).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) c1 = true
    rw [hstamp1]
    exact occurrenceBefore_mono hc hstamp

/-- For an honest `v`, `T2 ≤ T1` and `c2 ≤ c1`, an interpreted input at `v`'s read before `T2` whose
    head covers `B` is an interpreted input at `v`'s read before `T1`, provided that read's
    finalized block precedes `B`. -/
theorem q10_interpreted_fwd_cover (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest) {T2 T1 : Time}
    (h21 : T2 ≤ T1) {c1 c2 : Time} (hc : c2 ≤ c1) (eta r : Round) (sender : V)
    (B : Block V)
    (hFB : Block.Preceq (NamedRun.stateBeforeTime S rho T1 v).st.core.F B)
    {u : Protocol.SGVote V}
    (hu : u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho T2 v).st.core.F eta r c2 sender)
    (hcov : localCovers (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView
      u.confirmed B = true) :
    u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho T1 v).st.core.F eta r c1 sender := by
  have sch := core.toNamedScheduleWellFormed
  obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
  refine Finset.mem_filter.mpr
    ⟨q10_rawInputs_fwd S rho sch v h21 hc eta r sender hraw, ?_⟩
  cases hconf : u.confirmed with
  | none =>
    rw [hconf] at hcov
    simp only [localCovers, Protocol.head_covers] at hcov
    exact absurd hcov (by simp)
  | some root =>
    rw [hconf] at hcov
    simp only [localCovers, Protocol.head_covers] at hcov
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
    cases hf : Block.find?
        (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView.T root with
    | none => rw [hf] at hready; exact absurd hready (by simp)
    | some H =>
      rw [hf, Bool.and_eq_true] at hready
      rw [hf] at hcov
      have hBH : Block.Preceq B H := hcov
      have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T2 v).st :=
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T2 v).1.1.1
      have hHmem : H ∈ (NamedRun.stateBeforeTime S rho T2 v).st.core.T :=
        Proofs.HealingLemmas.find?_mem hf
      rw [hcoh.1] at hHmem
      obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
      obtain ⟨_, hstampeq⟩ := q10_strict_body_carry S rho sch v h21 hHn
      rw [q10_find_fwd S rho core v hv h21 hf, Bool.and_eq_true]
      constructor
      · have hs2 : stampedBefore
            (NamedRun.stateBeforeTime S rho T2 v).st.core.timestamp_block c2 Hn.erase = true := by
          simpa only [hHe, Protocol.Store.toHealing, Protocol.HealingStore.gradeView] using hready.1
        have hs1 : stampedBefore
            (NamedRun.stateBeforeTime S rho T1 v).st.core.timestamp_block c1 Hn.erase = true := by
          rw [stampedBefore_eq_occurrenceBefore] at hs2 ⊢
          rw [hstampeq]
          exact occurrenceBefore_mono hc hs2
        simpa only [hHe, Protocol.Store.toHealing, Protocol.HealingStore.gradeView] using hs1
      · simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (Block.preceq_trans hFB hBH)

/-! ## The grade at the two reads -/

theorem q10_gradeBool_transport (E : Env V) (gva gvb : Protocol.GradeView V)
    (Fa Fb : Block V) (eta r : Round) (ea la eb lb : Time) (B : Block V)
    (hea_la : ∀ w, readyView gva Fa eta r ea w ⊆ readyView gva Fa eta r la w)
    (hla_ra : ∀ w, readyView gva Fa eta r la w ⊆ rawView gva eta r la w)
    (heb_lb : ∀ w, readyView gvb Fb eta r eb w ⊆ readyView gvb Fb eta r lb w)
    (hlb_rb : ∀ w, readyView gvb Fb eta r lb w ⊆ rawView gvb eta r lb w)
    (heb_la : ∀ w, readyView gvb Fb eta r eb w ⊆ readyView gva Fa eta r la w)
    (hlb_la : ∀ w, readyView gvb Fb eta r lb w ⊆ readyView gva Fa eta r la w)
    (hrb_ra : ∀ w, rawView gvb eta r lb w ⊆ rawView gva eta r la w)
    (hkeep : ∀ w, ∀ u ∈ readyView gva Fa eta r ea w,
      localCovers gva u.key B = true → u ∈ readyView gvb Fb eta r eb w)
    (hcov : ∀ k, localCovers gva k B = true → localCovers gvb k B = true)
    (hgrade : gradeBool E gva Fa eta r ea la B = true) :
    gradeBool E gvb Fb eta r eb lb B = true := by
  have hpos : ∀ w, positive gva Fa eta r ea la w B = true →
      positive gvb Fb eta r eb lb w B = true := by
    intro w h
    simp only [positive, decide_eq_true_eq] at h ⊢
    exact q10_supports_transport _ _ (hkeep w) (heb_la w) (hlb_la w) (hrb_ra w)
      (fun x hx => hla_ra w (hea_la w hx)) (fun x hx => hla_ra w (heb_la w hx)) hcov h
  have hopp : ∀ w, opposing gvb Fb eta r eb lb w B = true →
      opposing gva Fa eta r ea la w B = true := by
    intro w h1
    simp only [opposing, decide_eq_true_eq] at h1 ⊢
    by_contra hno
    rcases Finset.eq_empty_or_nonempty (readyView gva Fa eta r ea w) with hemp | hne
    · refine hno (q10_opposes_transport _ _ ?_ (hlb_la w) (hrb_ra w) hcov h1)
      rw [hemp]
      exact Finset.empty_subset _
    · have hsa := q10_supports_of_not_opposes _ (hea_la w) hne hno
      have hsb := q10_supports_transport _ _ (hkeep w) (heb_la w) (hlb_la w) (hrb_ra w)
        (fun x hx => hla_ra w (hea_la w hx)) (fun x hx => hla_ra w (heb_la w hx)) hcov hsa
      exact q10_not_opposes_of_supports _ (heb_lb w) (hlb_rb w) hsb h1
  simp only [gradeBool, decide_eq_true_eq] at hgrade ⊢
  have hsub1 : (Finset.univ.filter fun w => opposing gvb Fb eta r eb lb w B = true) ⊆
      Finset.univ.filter fun w => opposing gva Fa eta r ea la w B = true := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hopp w (Finset.mem_filter.mp hw).2⟩
  have hsub2 : (Finset.univ.filter fun w => positive gva Fa eta r ea la w B = true) ⊆
      Finset.univ.filter fun w => positive gvb Fb eta r eb lb w B = true := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hpos w (Finset.mem_filter.mp hw).2⟩
  have e1 := E.electorate.weightOf_mono hsub1
  have e2 := E.electorate.weightOf_mono hsub2
  omega

/-- A block that is G2-graded at an honest node's round-`r` G2 domain time, and that the node's
    finalized block at the G1 domain time precedes, is G1-graded at the G1 domain time. -/
theorem q10_grade_cross (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) (hv : v ∈ rho.honest) (r : Round) (hr : 0 < r) (B : Block V)
    (hFB : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F B)
    (hgrade : gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) B = true) :
    gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g1) (late S.E S.hc r .g1) B = true := by
  have sch := core.toNamedScheduleWellFormed
  have h21 : domain S.E S.hc r .g2 ≤ domain S.E S.hc r .g1 :=
    (q10_domain_g2_lt_domain_g1 S r).le
  have hearly : early S.E S.hc r .g1 ≤ domain S.E S.hc r .g2 := q10_early_g1_le_domain_g2 S r
  have hlate : late S.E S.hc r .g1 ≤ domain S.E S.hc r .g2 := q10_late_g1_le_domain_g2 S r
  refine q10_gradeBool_transport S.E _ _ _ _ S.hc.η_SG r _ _ _ _ B
    (fun w => q10_readyView_cut _ _ _ _ (q10_early_le_late S r .g2) w)
    (fun w => q10_ready_subset_raw _ _ _ _ _ w)
    (fun w => q10_readyView_cut _ _ _ _ (q10_early_le_late S r .g1) w)
    (fun w => q10_ready_subset_raw _ _ _ _ _ w)
    (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun w => ?_)
    (fun k hk => q10_localCovers_fwd S rho core v hv h21 k B hk) hgrade
  · exact (Finset.image_subset_image (q10_interpreted_back S rho core v hv
      (q10_early_g1_public S r hr) hearly h21 S.hc.η_SG r w)).trans
      (q10_readyView_cut _ _ _ _ hearly w)
  · exact (Finset.image_subset_image (q10_interpreted_back S rho core v hv
      (q10_late_g1_public S r hr) hlate h21 S.hc.η_SG r w)).trans
      (q10_readyView_cut _ _ _ _ hlate w)
  · exact (Finset.image_subset_image (q10_rawInputs_back S rho sch v
      (q10_late_g1_public S r hr) hlate (hlate.trans h21) S.hc.η_SG r w)).trans
      (q10_rawView_cut _ _ _ hlate w)
  · intro u hu hcov
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    subst hxu
    exact Finset.mem_image_of_mem _ (q10_interpreted_fwd_cover S rho core v hv h21
      (q10_early_g2_le_early_g1 S r) S.hc.η_SG r w B hFB hx hcov)

/-! ## Frame algebra -/

omit [Fintype V] in
/-- Block compatibility is symmetric. -/
theorem q10_compatible_symm {B C : Block V} (h : Block.compatible B C = true) :
    Block.compatible C B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at h ⊢
  exact h.symm

omit [Fintype V] in
/-- Two blocks covered by the same key are compatible. -/
theorem q10_covers_compatible (gv : Protocol.GradeView V) {k : Option BlockId}
    {B B' : Block V} (hB : localCovers gv k B = true) (hB' : localCovers gv k B' = true) :
    Block.compatible B B' = true := by
  unfold localCovers Protocol.head_covers at hB hB'
  rcases Option.eq_none_or_eq_some k with hkr | ⟨root, hkr⟩
  · rw [hkr] at hB
    exact absurd hB (by simp)
  · rw [hkr] at hB hB'
    dsimp only at hB hB'
    rcases Option.eq_none_or_eq_some (Block.find? gv.T root) with hf | ⟨H, hf⟩
    · rw [hf] at hB
      exact absurd hB (by simp)
    · rw [hf] at hB hB'
      exact Block.compatible_of_preceq_common hB hB'

omit [Fintype V] in
/-- A validator positive for `B` is opposing for every block incompatible with `B`. -/
theorem q10_opposing_of_positive (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {e l : Time} (hel : e ≤ l) (u : V) {B B' : Block V}
    (hne : Block.compatible B B' = false)
    (hpos : positive gv F eta r e l u B = true) :
    opposing gv F eta r e l u B' = true := by
  simp only [positive, decide_eq_true_eq] at hpos
  obtain ⟨x, hx, hmax, hcov, -, -⟩ := hpos
  simp only [opposing, decide_eq_true_eq]
  refine Or.inl ⟨x, q10_readyView_cut gv F eta r hel u hx, hmax, ?_⟩
  intro hcov'
  rw [q10_covers_compatible gv hcov hcov'] at hne
  exact absurd hne (by simp)

/-- Two blocks graded in the same view are compatible. -/
theorem q10_graded_compatible (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {e l : Time} (hel : e ≤ l) {B B' : Block V}
    (hB : gradeBool E gv F eta r e l B = true)
    (hB' : gradeBool E gv F eta r e l B' = true) : Block.compatible B B' = true := by
  by_contra hcon
  have hne : Block.compatible B B' = false := by
    simpa only [Bool.not_eq_true] using hcon
  have hne' : Block.compatible B' B = false := by
    by_contra h
    exact hcon (q10_compatible_symm (by simpa only [Bool.not_eq_false] using h))
  simp only [gradeBool, decide_eq_true_eq] at hB hB'
  have hsub : (Finset.univ.filter fun w => positive gv F eta r e l w B = true) ⊆
      Finset.univ.filter fun w => opposing gv F eta r e l w B' = true := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      q10_opposing_of_positive gv F eta r hel w hne (Finset.mem_filter.mp hw).2⟩
  have hsub' : (Finset.univ.filter fun w => positive gv F eta r e l w B' = true) ⊆
      Finset.univ.filter fun w => opposing gv F eta r e l w B = true := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      q10_opposing_of_positive gv F eta r hel w hne' (Finset.mem_filter.mp hw).2⟩
  have h1 := E.electorate.weightOf_mono hsub
  have h2 := E.electorate.weightOf_mono hsub'
  omega

/-- A graded member of the tree precedes the freeze root, which therefore exists. -/
theorem q10_freeze_of_graded (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {e l : Time} (hel : e ≤ l) {B : Block V}
    (hmem : B ∈ gv.T) (hgrade : gradeBool E gv F eta r e l B = true) :
    ∃ raw : Block V, freezeRoot E gv F eta r e l = some raw ∧ Block.Preceq B raw := by
  have hBT : B ∈ gv.T.filter fun X => gradeBool E gv F eta r e l X = true :=
    Finset.mem_filter.mpr ⟨hmem, hgrade⟩
  have hcmp : ∀ X ∈ gv.T.filter fun X => gradeBool E gv F eta r e l X = true,
      ∀ Y ∈ gv.T.filter fun X => gradeBool E gv F eta r e l X = true,
      Block.compatible X Y = true := by
    intro X hX Y hY
    exact q10_graded_compatible E gv F eta r hel (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨raw, hraw⟩ := Option.isSome_iff_exists.mp
    (Proofs.HealingSurface.deepest?_isSome_of_compatible hcmp ⟨B, hBT⟩)
  refine ⟨raw, hraw, Proofs.HealingLemmas.deepest?_dominates hraw hBT
    (hcmp B hBT raw (Proofs.Engine.deepest?_mem hraw))⟩

omit [Fintype V] in
/-- Clipping `g` against `F` gives an ancestor of `g`. -/
theorem q10_clip_preceq (g F : Block V) :
    Block.Preceq (DecoupledConsensusModel.Protocol.clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats w ih =>
    simp only [DecoupledConsensusModel.Protocol.clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

omit [Fintype V] in
/-- For `B` compatible with `F`, `B` precedes the clip of `g` against `F` if and only if `B`
    precedes `g`. -/
theorem q10_retained_prefix (g F B : Block V) (hBF : Block.compatible B F = true) :
    Block.Preceq B (DecoupledConsensusModel.Protocol.clipGrade g F) ↔ Block.Preceq B g := by
  constructor
  · intro h
    exact Block.preceq_trans h (q10_clip_preceq g F)
  · induction g with
    | genesis => exact fun h => h
    | node p s root gv gsv ats w ih =>
      intro hBg
      by_cases hGF : Block.compatible (.node p s root gv gsv ats w) F = true
      · simpa only [DecoupledConsensusModel.Protocol.clipGrade, hGF, ↓reduceIte] using hBg
      · have hBp : Block.Preceq B p := by
          simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBg
          rcases hBg with hEq | hBp
          · subst B
            exact False.elim (hGF hBF)
          · exact hBp
        simpa only [DecoupledConsensusModel.Protocol.clipGrade, hGF,
          Bool.eq_false_iff.mpr hGF, Bool.false_eq_true, ↓reduceIte] using ih hBp

omit [Fintype V] in
/-- The finalized block precedes every member of the filtered tree. -/
theorem q10_filtered_F {st : Protocol.FGStore V} {B : Block V}
    (h : B ∈ Protocol.get_filtered_block_tree st) : Block.Preceq st.F B := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants, Finset.mem_filter] at h
  exact h.1.1.2

omit [Fintype V] in
/-- When a member `q` of `T` precedes `root`, the active prefix of `root` in `T` exists and `q`
    precedes it. -/
theorem q10_activePrefix_dominates {T : Finset (Block V)} {root q : Block V}
    (hq : q ∈ T) (hqr : Block.Preceq q root) :
    ∃ X : Block V, activePrefix T root = some X ∧ Block.Preceq q X := by
  set U := T.filter fun B => Block.preceq B root = true with hU
  have hqU : q ∈ U := Finset.mem_filter.mpr ⟨hq, hqr⟩
  have hcmp : ∀ X ∈ U, ∀ Y ∈ U, Block.compatible X Y = true := by
    intro X hX Y hY
    exact Block.compatible_of_preceq_common (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp
    (Proofs.HealingSurface.deepest?_isSome_of_compatible hcmp ⟨q, hqU⟩)
  exact ⟨X, hX, Proofs.HealingLemmas.deepest?_dominates hX hqU
    (hcmp q hqU X (Proofs.Engine.deepest?_mem hX))⟩

/-- The tree of a node's read only grows with time. -/
theorem q10_tree_fwd (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) {T2 T1 : Time} (h21 : T2 ≤ T1) {B : Block V}
    (h : B ∈ (NamedRun.stateBeforeTime S rho T2 v).st.core.toHealing.gradeView.T) :
    B ∈ (NamedRun.stateBeforeTime S rho T1 v).st.core.toHealing.gradeView.T := by
  have sch := core.toNamedScheduleWellFormed
  have hcoh2 : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T2 v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T2 v).1.1.1
  have hcoh1 : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho T1 v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho T1 v).1.1.1
  have h2 : B ∈ (NamedRun.stateBeforeTime S rho T2 v).st.core.T := h
  rw [hcoh2.1] at h2
  obtain ⟨Bn, hBn, hBe⟩ := Finset.mem_image.mp h2
  have h1 : B ∈ (NamedRun.stateBeforeTime S rho T1 v).st.core.T := by
    rw [hcoh1.1]
    exact hBe ▸ Finset.mem_image_of_mem NamedBlock.erase
      ((q10_strict_body_carry S rho sch v h21 hBn).1)
  exact h1

/-! ## The round-`r` G1 freeze root from the G2 freeze root -/

/-- If an honest node's round-`r` G2 freeze root `g2` is preceded by the node's finalized block at
    the G1 domain time, then the round-`r` G1 freeze root exists and `g2` precedes it. -/
theorem q10_g1_of_g2_freeze (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest)
    (r : Round) (hr : 0 < r) (g2 : Block V)
    (hg2raw : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some g2)
    (hFB : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F g2) :
    ∃ g1 : Block V,
      freezeRoot S.E
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F S.hc.η_SG r
          (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some g1 ∧
        Block.Preceq g2 g1 := by
  have hmemfilter := Proofs.Engine.deepest?_mem hg2raw
  have hmem2 := (Finset.mem_filter.mp hmemfilter).1
  have hgrade2 := (Finset.mem_filter.mp hmemfilter).2
  have hgrade1 := q10_grade_cross S rho core v hv r hr g2 hFB hgrade2
  have hmem1 := q10_tree_fwd S rho core v (q10_domain_g2_lt_domain_g1 S r).le hmem2
  exact q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F
    S.hc.η_SG r (q10_early_le_late S r .g1) hmem1 hgrade1

#print axioms q10_g1_of_g2_freeze

/-! ## The grade-2 block precedes the anchor -/

/-- When the frame's two slots hold an honest node's round-`r` G2 and G1 freeze roots clipped
    against `st.F`, and the node's finalized block at the G1 domain time precedes `st.F`, the
    frame's grade-2 block precedes the anchor. -/
theorem q10_frame_core (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest) (r : Round) (hr : 0 < r)
    (st : Protocol.HealingStore V) (frame : DecoupledConsensusModel.Protocol.Frame V)
    (hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F st.F)
    (hg2 : frame.g2 = some ((freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2)).map
        (fun X => DecoupledConsensusModel.Protocol.clipGrade X st.F)))
    (hg1 : frame.g1 = some ((freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1)).map
        (fun X => DecoupledConsensusModel.Protocol.clipGrade X st.F)))
    (q : Block V)
    (hq : DecoupledConsensusModel.Protocol.grade2Block st frame = some q) :
    Block.Preceq q (DecoupledConsensusModel.Protocol.anchor S.E S.hc st r frame.g1) := by
  unfold DecoupledConsensusModel.Protocol.grade2Block at hq
  by_cases hcl : DecoupledConsensusModel.Protocol.allClosed frame = true
  swap
  · rw [if_neg hcl] at hq
    exact absurd hq (by simp)
  rw [if_pos hcl, hg2, Option.bind_some, id_eq] at hq
  obtain ⟨g2c, hg2c, hact⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨g2, hg2raw, hclip⟩ := Option.map_eq_some_iff.mp hg2c
  have hqmem : q ∈ Protocol.get_filtered_block_tree st.toFG :=
    NamedProposalParent.activePrefix_mem _ g2c q hact
  have hqle : Block.Preceq q g2c := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hact
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hact)).2
  have hFq : Block.Preceq st.F q := q10_filtered_F hqmem
  have hcompatq : Block.compatible q st.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFq
  have hclip' : DecoupledConsensusModel.Protocol.clipGrade g2 st.F = g2c := hclip
  have hqg2 : Block.Preceq q g2 := by
    refine (q10_retained_prefix g2 st.F q hcompatq).mp ?_
    rw [hclip']
    exact hqle
  have hFB : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F g2 :=
    Block.preceq_trans hFmono (Block.preceq_trans hFq hqg2)
  obtain ⟨g1, hfz1, hg2g1⟩ := q10_g1_of_g2_freeze S rho core v hv r hr g2 hg2raw hFB
  have hg1' : frame.g1 = some (some (DecoupledConsensusModel.Protocol.clipGrade g1 st.F)) := by
    rw [hg1, hfz1]
    rfl
  have hqclip : Block.Preceq q (DecoupledConsensusModel.Protocol.clipGrade g1 st.F) :=
    (q10_retained_prefix g1 st.F q hcompatq).mpr (Block.preceq_trans hqg2 hg2g1)
  obtain ⟨X, hX, hqX⟩ := q10_activePrefix_dominates hqmem hqclip
  rw [hg1']
  change Block.Preceq q ((DecoupledConsensusModel.Protocol.activePrefix
    (Protocol.get_filtered_block_tree st.toFG)
    (DecoupledConsensusModel.Protocol.clipGrade g1 st.F)).getD
      (Protocol.get_fg_root st.toFG))
  rw [hX, Option.getD_some]
  exact hqX

private theorem q10_dom_arith : ∀ x d : Int, 0 < d →
    x + 1 * d < x + 6 * d ∧ x + 0 * d < x + 6 * d ∧ x + (-1) * d < x + 6 * d := by
  intro x d h
  exact ⟨by omega, by omega, by omega⟩

/-- Every phase domain time of round `r` is before the round's action time `S.a r`. -/
theorem q10_domain_lt_a (S : Setup V) (r : Round) (p : Phase) :
    domain S.E S.hc r p < S.a r := by
  have ha : S.a r = opening S.E S.hc r + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, opening, Protocol.proposal_time, Env.t]
  have hdom : domain S.E S.hc r p = opening S.E S.hc r + p.domainOffset * S.E.Δ := rfl
  obtain ⟨h1, h0, hm⟩ := q10_dom_arith (opening S.E S.hc r) S.E.Δ S.E.Δ_pos
  rw [ha, hdom]
  cases p with
  | g0 => exact h1
  | g1 => exact h0
  | g2 => exact hm


/-- At an included round, the grade-2 block of an honest node's checkpoint precedes the checkpoint's
    anchor. -/
theorem grade2_preceq_anchor_at_checkpoint (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest) (b0 : Time) (r : Round)
    (hinc : RoundIncluded S rho b0 r) (q : Block V)
    (hq : DecoupledConsensusModel.Protocol.grade2Block (checkpoint S rho v r).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
        (checkpoint S rho v r).st.core.toHealing r) = some q) :
    Block.Preceq q (DecoupledConsensusModel.Protocol.anchor S.E S.hc
      (checkpoint S rho v r).st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
        (checkpoint S rho v r).st.core.toHealing r).g1) := by
  have sch := core.toNamedScheduleWellFormed
  have hr : 0 < r := hinc.1
  have h21 : domain S.E S.hc r .g2 ≤ domain S.E S.hc r .g1 :=
    (q10_domain_g2_lt_domain_g1 S r).le
  have hhor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    (q10_domain_lt_a S r .g1).le.trans hinc.2.2
  refine q10_frame_core S rho core v hv r hr _ _ ?_ ?_ ?_ q hq
  · show Block.Preceq (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.F
    rw [strict_read_eq_index S rho sch.sorted (domain S.E S.hc r .g1),
      strict_read_eq_index S rho sch.sorted (S.a r)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
      (strict_lengths_mono rho (q10_domain_lt_a S r .g1).le)
  · exact FrameForward.frame_phase_checkpoint_eq S rho v r .g2 _
      (FrameCompleted.frame_phase_completed S rho core v hv r hr .g2 (S.a r)
        (q10_domain_lt_a S r .g2) le_rfl (h21.trans hhor))
  · exact FrameForward.frame_phase_checkpoint_eq S rho v r .g1 _
      (FrameCompleted.frame_phase_completed S rho core v hv r hr .g1 (S.a r)
        (q10_domain_lt_a S r .g1) le_rfl hhor)

#print axioms q10_gradeBool_transport
#print axioms q10_grade_cross
#print axioms q10_frame_core
#print axioms grade2_preceq_anchor_at_checkpoint

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
