module
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Statements.Executions.SupporterDefs
public import GoldilocksCorrectness.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Executions.CountAgreement

@[expose] public section

/-!
# Lemmas 62 to 64: the Goldfish vote argument over reading points

The proofs of the theorems stated in
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`. Each takes the times at
which it reads a validator's node state as parameters (`t_e` the early cutoff, `t_f` the cutoff on
the stamps of the votes and blocks the voter `w` counts, `t_w` the time `w`'s state is read, `t_v`
the time `v`'s state is read), with the inequalities between them as hypotheses:

- Lemma 62: a vote that resolved before `t_e` at `v₁` was in `v₁`'s pool before `t_e`, and reaches
  `v₂` by `t_e + Δ` (`pool_vote_reaches_before_add_delay`);
- Lemma 63: each early supporter's vote reaches `w` before `t_f`, its head block too, and every
  slot-`s` vote of the supporter that `w` re-sent before `t_w` reaches `v` before `t_v`, where the
  supporter has one vote; then the two readings, on the sets `w` counts and on `w`'s pool;
- Lemma 64: Lemma 6, Lemma 7 and Lemma 2 on `w`'s walk, with the counted sets of Lemma 63.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_natCast)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff mem_included_support_votes_iff
  mem_included_votes_iff)

open GoldilocksCorrectness.Proofs.Routines (voters_count_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  VotesOnceInPoolFor CountedVotesAt VoterTreeAt)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  fc_root_ancestorEq_get_anchor ac_valid_payload_facts tau_eq_some_blockStamp
  occurrenceBefore_eq_true_iff tau_eq_some_stamp mem_participants_iff
  compatible_of_ancestorEq_compatible tau_eq_ok_some)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; core's `get_elem_tactic` searches the whole context before it
-- tries `trivial`, which in a context of many hypotheses can exhaust the heartbeats
--. This rule, local to the file, is
-- tried first and proves `True` at once; on any other goal it fails and the search continues.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Lemma 62, a vote that resolved early at one validator reaches another within one delay of the
early cutoff. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery premises up to `b`, the latest deadline being `t_e + Δ S` (`v₁`'s
re-send reaching `v₂`). -/
theorem lem62_early_vote_reaches_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_v t_w b : ℕ) (v₁ v₂ : V) (Φ : Frame V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hGST : GST ≤ t_e)
    (h02 : t_e + Δ S ≤ t_w)
    (hhi : t_e + Δ S < slotStart S (s + 2))
    (hv₂ : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S →
      v₂ ∈ Sched.awake (t : Int) ∧ v₂ ∉ Sched.adv (t : Int))
    -- the latest deadline the proof reads is at most the bound
    (hb : t_e + Δ S ≤ b) :
    ∀ vote ∈ (stateBefore x t_v v₁).A.pool s,
      (∃ y : Stamp, (stateBefore x t_v v₁).A.tau Φ vote = .ok (some y) ∧
        occurrenceBefore (some y) ((t_e : ℕ) : Int) = true) →
      vote ∈ (stateBefore x t_w v₂).A.pool s ∨
        ∃ u₁ ∈ (stateBefore x t_w v₂).A.pool s, ∃ u₂ ∈ (stateBefore x t_w v₂).A.pool s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  intro vote hvote ⟨y, hτ, hy⟩
  -- the vote resolves strictly before `t_e`, so its stamp is strictly before `t_e`, and `v₁` held
  -- it before `t_e`
  obtain ⟨y', hyy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hy
  cases hyy
  obtain ⟨τ, hts, hτy⟩ := tau_eq_some_stamp hτ
  have hv0 : vote ∈ (stateBefore x t_e v₁).A.pool s :=
    (voteStamp_lt_iff hDiv hvote).1 ⟨τ, hts, lt_of_le_of_lt hτy hlt⟩
  -- the relay from `t_e`, then the pool grows up to `t_w`
  have hle : stepBefore x (t_e + Δ S) ≤ stepBefore x t_w := stepBefore_mono x hDiv h02
  rcases pool_vote_reaches_before_add_delay_upTo S Sched x hDiv hMono GST hSync hCatch t_e
      s v₁ v₂ vote hGST hhi hv₂ hv0 hb with h | ⟨u₁, h₁, u₂, h₂, hne, hi₁, hi₂⟩
  · exact Or.inl (pool_mono x v₂ hle s h)
  · exact Or.inr ⟨u₁, pool_mono x v₂ hle s h₁, u₂, pool_mono x v₂ hle s h₂, hne, hi₁, hi₂⟩

/-- Lemma 63, the early supporters' votes and heads reach the next slot's voter, and are its only
votes of their validators. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(`w`'s re-sends reaching `v`; the re-sends from `v` reach `w` by `t_e + Δ S ≤ t_w + Δ S`). -/
theorem lem63_supporters_counted_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ t_e)
    (h1 : 1 ≤ t_e)
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    (hslot : t_e < slotStart S (s + 1))
    (hhi : t_w + Δ S < slotStart S (s + 2))
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    (hF : (stateBefore x t_w w).S.F.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup, ∃ vote_u ∈ (stateBefore x t_f w).A.pool s, vote_u.val_index = u ∧
      (∃ τ : Stamp, (stateBefore x t_w w).A.timestamp_vote vote_u = some τ ∧
        τ < (((t_f : ℕ) : Int) : Stamp)) ∧
      (∃ H_u ∈ (stateBefore x t_f w).S.T, H_u.root = vote_u.head ∧ B.AncestorEq H_u ∧
        H_u.slot ≤ s ∧
        ∃ st : Stamp, (stateBefore x t_w w).A.timestamp_block H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
      ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
        (∃ j < stepBefore x t_w,
          (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
            x[j + 1].sent - x[j].sent ∧
          w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time) →
        vote' = vote_u) ∧
    (∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      (∃ j < stepBefore x t_w,
        (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
          x[j + 1].sent - x[j].sent ∧
        w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time) →
      vote' ∈ (stateBefore x t_v v).A.pool s ∨
        ∃ v₁ ∈ (stateBefore x t_v v).A.pool s, ∃ v₂ ∈ (stateBefore x t_v v).A.pool s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index) := by
  have hΔ := one_le_Δ S
  have hRootsΦv : RootsNameBlocksIn (fg_to_ac (stateBefore x t_v v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- `t_e` lies in slot `s` or earlier
  have hslot₀ : S.C.slot ((t_e : ℕ) : Int) ≤ s := by
    rw [slot_natCast]
    rw [slotStart_eq] at hslot
    exact Nat.lt_succ_iff.1
      ((Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [Nat.mul_comm]; exact hslot))
  -- a vote of slot `s` that `w` re-sent before `t_w` reaches `v`'s pool before `t_v`, or `v` holds
  -- two votes of its validator there
  have hToV : ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      (∃ j < stepBefore x t_w,
        (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
          x[j + 1].sent - x[j].sent ∧
        w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time) →
      vote' ∈ (stateBefore x t_v v).A.pool s ∨
        ∃ v₁ ∈ (stateBefore x t_v v).A.pool s, ∃ v₂ ∈ (stateBefore x t_v v).A.pool s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index := by
    intro vote' hs' hcomm' ⟨j, hj, hsend, hhon, hlo⟩
    have hjt : x[j + 1].time < t_w := (lt_stepBefore_iff x hDiv).1 hj
    have hres := relayed_vote_in_pool_before_add_delay_upTo S Sched x hDiv hMono GST hSync hCatch
      j t_w w v vote' hsend hhon hlo (le_of_lt hjt) (by omega)
      (by rw [hs']; exact hcomm') (by rw [hs']; exact hhi) hv hb
    have hle : stepBefore x (t_w + Δ S) ≤ stepBefore x t_v := stepBefore_mono x hDiv h23
    rw [hs'] at hres
    rcases hres with h | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · exact Or.inl (pool_mono x v hle s h)
    · exact Or.inr ⟨v₁, pool_mono x v hle s h₁, v₂, pool_mono x v hle s h₂, hne, hi₁, hi₂⟩
  -- a vote of slot `s` of a member `u` of `Sup` that `w` re-sent before `t_w` is `u`'s only vote
  -- at `v`: it reaches `v`'s pool before `t_v`, where `u` has exactly one vote
  have hOnce : ∀ u : V, ∀ vote_u : GoldfishVote V,
      (∀ vote' ∈ (stateBefore x t_v v).A.pool s, vote'.val_index = u → vote' = vote_u) →
      u ∈ S.P.committee s →
      ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
        (∃ j < stepBefore x t_w,
          (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
            x[j + 1].sent - x[j].sent ∧
          w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time) →
        vote' = vote_u := by
    intro u vote_u huniq hcomm vote' hs' hi' hrel
    rcases hToV vote' hs' (by rw [hi']; exact hcomm) hrel with h | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · exact huniq vote' h hi'
    · exact absurd ((huniq v₁ h₁ (hi₁.trans hi')).trans (huniq v₂ h₂ (hi₂.trans hi')).symm) hne
  -- `v` is honest at `t_e`, since it is honest at `t_w` and corruption is permanent
  have hvc : v ∉ Sched.adv ((t_e : ℕ) : Int) := fun h =>
    (hv t_w le_rfl (by omega)).2 (hMono _ _ (by exact_mod_cast (show t_e ≤ t_w by omega)) h)
  have hle01 : stepBefore x (t_e + Δ S) ≤ stepBefore x t_f := stepBefore_mono x hDiv h01
  have hle12 : stepBefore x t_f ≤ stepBefore x t_w := stepBefore_mono x hDiv h12
  have hle02 : stepBefore x (t_e + Δ S) ≤ stepBefore x t_w := le_trans hle01 hle12
  refine ⟨?_, hToV⟩
  intro u hu
  obtain ⟨vote_u, hpv, hidx, ⟨H_u, hHΦv, hroot, hBH⟩, ⟨y, hy, hyb⟩, huniq⟩ := hSup u hu
  -- the vote's slot and committee
  have hsu : vote_u.slot = s := pool_slot_of_stateBefore S Sched x _ v s vote_u hpv
  have hcomm : u ∈ S.P.committee s := by
    rw [← hidx]
    exact pool_committee_of_stateBefore S Sched x _ v s vote_u hpv
  -- the vote resolves strictly before `t_e`, so it was in `v`'s pool before `t_e`
  obtain ⟨y', hyy', hyc⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
  cases hyy'
  obtain ⟨τ, hτ, hτy⟩ := tau_eq_some_stamp hy
  have hpc : vote_u ∈ (stateBefore x t_e v).A.pool s :=
    (voteStamp_lt_iff hDiv hpv).1 ⟨τ, hτ, lt_of_le_of_lt hτy hyc⟩
  -- `v`'s re-send reaches `w` before `t_e + Δ`; `w` cannot hold two votes of `u` there
  have hpw : vote_u ∈ (stateBefore x (t_e + Δ S) w).A.pool s := by
    rcases pool_vote_reaches_before_add_delay_upTo S Sched x hDiv hMono GST hSync hCatch
        t_e s v w vote_u hGST (by omega) hw hpc (by omega) with
      h | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · exact h
    · exfalso
      have hrel : ∀ vj ∈ (stateBefore x (t_e + Δ S) w).A.pool s, vj.val_index = u →
          vj = vote_u := by
        intro vj hvj hij
        have hvj2 := pool_mono x w hle02 s hvj
        have hsj := pool_slot_of_stateBefore S Sched x _ w s vj hvj2
        obtain ⟨k, hk, hsk, hhk, hlk⟩ :=
          pool_vote_relayed_before S Sched x hMono _ w s vj hvj2
        exact hOnce u vote_u huniq hcomm vj hsj hij ⟨k, hk, hsk, hhk, by rw [hsj]; exact hlk⟩
      exact hne ((hrel v₁ h₁ (hi₁.trans hidx)).trans (hrel v₂ h₂ (hi₂.trans hidx)).symm)
  have hpw1 : vote_u ∈ (stateBefore x t_f w).A.pool s := pool_mono x w hle01 s hpw
  have hpw2 : vote_u ∈ (stateBefore x t_w w).A.pool s := pool_mono x w hle12 s hpw1
  -- `H_u` was in `v`'s tree before `t_e`, and reaches `w` before `t_e + Δ`
  have hHTv : H_u ∈ (stateBefore x t_v v).S.T := ((mem_fg_to_ac_tree _ _).1 hHΦv).1
  obtain ⟨τH', hτH', hτH'y⟩ := tau_eq_some_blockStamp hRootsΦv hHΦv hroot hy
  have hHc : H_u ∈ (stateBefore x t_e v).S.T :=
    (blockStamp_lt_iff hDiv hHTv).1 ⟨τH', hτH', lt_of_le_of_lt hτH'y hyc⟩
  have hcompat : (stateBefore x (t_e + Δ S) w).S.F.compatible H_u = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (stateBefore_grows x hDiv w (show t_e + Δ S ≤ t_w by omega)).2.1 (ancestorEq_trans hF hBH)))
  have hHfr : H_u ∈ (stateBefore x (t_e + Δ S) w).S.T :=
    mem_T_before_add_delay_upTo hDiv hMono (SynchronyFromWakeUpTo.mono (by omega) hSync)
      (CatchUpOnWakeUpTo.mono (by omega) hCatch) (hRoots.mono (by omega)) hParent h1 hGST
      hvc hHc hw hcompat
  have hHT1 : H_u ∈ (stateBefore x t_f w).S.T := mem_T_mono x w hle01 hHfr
  have hHT2 : H_u ∈ (stateBefore x t_w w).S.T := mem_T_mono x w hle12 hHT1
  refine ⟨vote_u, hpw1, hidx, (voteStamp_lt_iff hDiv hpw2).2 hpw1,
    ⟨H_u, hHT1, hroot, hBH, le_trans (slot_le_of_mem_T_before hDiv hMono hHc) hslot₀,
      (blockStamp_lt_iff hDiv hHT2).2 hHT1⟩, ?_⟩
  intro vote' hs' hi' hrel
  exact hOnce u vote_u huniq hcomm vote' hs' hi' hrel

/-- Lemma 63 read on the sets the voter counts: each early supporter votes once for `B`'s chain
among them, the voters are fewer than twice the supporters, and every support vote is counted. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls). -/
theorem supporters_vote_once_counted_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (votes support_votes : Finset (GoldfishVote V))
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ t_e)
    (h1 : 1 ≤ t_e)
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    (hslot : t_e < slotStart S (s + 1))
    (hhi : t_w + Δ S < slotStart S (s + 2))
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : voters_count ((stateBefore x t_v v).A.pool s) < 2 * Sup.card)
    (hF : (stateBefore x t_w w).S.F.AncestorEq B)
    (hCounted : CountedVotesAt (stateBefore x t_w w).A (fg_to_ac (stateBefore x t_w w).S)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup,
      VotesOnceFor (fg_to_ac (stateBefore x t_w w).S) votes support_votes s B u ∧
      ∃ H_u ∈ (stateBefore x t_w w).S.T, B.AncestorEq H_u ∧
        ∃ st : Stamp, (stateBefore x t_w w).A.timestamp_block H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
    voters_count votes < 2 * Sup.card ∧ support_votes ⊆ votes := by
  obtain ⟨hPer, hToV⟩ := lem63_supporters_counted_at S Sched x GST s t_e t_f t_w t_v b Sup B v w
    hDiv hMono hSync hCatch hRoots hParent hGST h1 h01 h12 h23 hslot hhi hw hv hSup hF hb
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x t_w w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  have hle12 : stepBefore x t_f ≤ stepBefore x t_w := stepBefore_mono x hDiv h12
  obtain ⟨hCv, hCs⟩ := hCounted
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- the blocks whose included votes `w` counts
  have hBne : ∀ B' : Block V, B'.slot = s + 1 → B' ≠ Block.genesis := by
    rintro B' hBs rfl
    exact Nat.succ_ne_zero s hBs.symm
  have hPayload : ∀ B' ∈ (fg_to_ac (stateBefore x t_w w).S).tree,
      B'.slot = s + 1 → ac_valid_payload S.P B' = true := by
    intro B' hB' hBs
    have hBT := ((mem_fg_to_ac_tree _ _).1 hB').1
    have hwf := (((lem11_node_invariant S Sched x (stepBefore x t_w) w).1.2.2.1).2
      B' hBT (hBne B' hBs)).2.1
    rw [block_well_formed_iff] at hwf
    exact hwf.1.2
  have hIncl : ∀ vote' ∈ included_votes (fg_to_ac (stateBefore x t_w w).S) (s + 1),
      ∃ B' ∈ (fg_to_ac (stateBefore x t_w w).S).tree,
        B'.slot = s + 1 ∧ vote' ∈ B'.votes ∧ vote'.slot = s := by
    intro vote' hv
    simp only [mem_included_votes_iff,
      Nat.add_sub_cancel] at hv
    obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hv
    exact ⟨B', hB', hBs, hvB, hvs⟩
  have hSupport : support_votes ⊆ votes := by
    intro vote' hv
    rcases (hCs vote').1 hv with ⟨hp', hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote').2 (Or.inl ⟨hp', hτ⟩)
    · simp only [mem_included_support_votes_iff,
        Nat.add_sub_cancel] at hinc
      obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hinc
      have hvB' : vote' ∈ B'.votes :=
        (ac_valid_payload_facts S.P B' (hPayload B' hB' hBs)).2.1 vote' hvB
      refine (hCv vote').2 (Or.inr ?_)
      simp only [mem_included_votes_iff,
        Nat.add_sub_cancel]
      exact ⟨B', ⟨hB', hBs⟩, hvB', hvs⟩
  -- every vote `w` counts is of slot `s`, from the slot-`s` committee, and was re-sent by `w`
  -- before `t_w`, as a pool vote or as a vote included in a block of `w`'s tree
  have hRelW : ∀ vote' ∈ votes, vote'.slot = s ∧ vote'.val_index ∈ S.P.committee s ∧
      ∃ j < stepBefore x t_w,
        (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
          x[j + 1].sent - x[j].sent ∧
        w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time := by
    intro vote' hv
    rcases (hCv vote').1 hv with ⟨hp', -⟩ | hinc
    · have hs' := pool_slot_of_stateBefore S Sched x _ w s vote' hp'
      obtain ⟨j, hj, hsend, hhon, hlo⟩ :=
        pool_vote_relayed_before S Sched x hMono _ w s vote' hp'
      exact ⟨hs', pool_committee_of_stateBefore S Sched x _ w s vote' hp', j, hj, hsend, hhon,
        by rw [hs']; exact hlo⟩
    · obtain ⟨B', hB', hBs, hvB, hvs⟩ := hIncl vote' hinc
      have hc' := (ac_valid_payload_facts S.P B' (hPayload B' hB' hBs)).2.2 vote' hvB
      rw [hBs, Nat.add_sub_cancel] at hc'
      exact ⟨hvs, hc', included_vote_relayed_before S Sched x hMono _ w B' vote'
        ((mem_fg_to_ac_tree _ _).1 hB').1 (hBne B' hBs) hvB⟩
  -- every validator with a vote `w` counts has a vote in `v`'s pool of slot `s`
  have hVoters : voters_count votes < 2 * Sup.card := by
    have hsub : participants votes ⊆ participants ((stateBefore x t_v v).A.pool s) := by
      intro u' hu'
      obtain ⟨vote', hv', hi'⟩ := (mem_participants_iff _ _).1 hu'
      obtain ⟨hs', hcomm', hrel⟩ := hRelW vote' hv'
      refine (mem_participants_iff _ _).2 ?_
      rcases hToV vote' hs' hcomm' hrel with h | ⟨v₁, h₁, -, -, -, hi₁, -⟩
      · exact ⟨vote', h, hi'⟩
      · exact ⟨v₁, h₁, hi₁.trans hi'⟩
    exact lt_of_le_of_lt (by rw [voters_count_eq, voters_count_eq]; exact Finset.card_le_card hsub)
      hEligible
  refine ⟨?_, hVoters, hSupport⟩
  -- each member of `Sup` votes once for `B`'s chain among the votes `w` counts
  intro u hu
  obtain ⟨vote_u, hpw1, hidx, ⟨τv, hτv, hτvlt⟩, ⟨H_u, hHT1, hroot, hBH, hHs, τH, hτH, hτHlt⟩,
    huniq⟩ := hPer u hu
  have hpw2 : vote_u ∈ (stateBefore x t_w w).A.pool s := pool_mono x w hle12 s hpw1
  have hsu : vote_u.slot = s := pool_slot_of_stateBefore S Sched x _ w s vote_u hpw1
  have hHT2 : H_u ∈ (stateBefore x t_w w).S.T := mem_T_mono x w hle12 hHT1
  have hHΦw : H_u ∈ (fg_to_ac (stateBefore x t_w w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hHT2, ancestorEq_trans hF hBH⟩
  have htau := tau_eq_ok_some hRootsΦ hHΦw hroot (by rw [hsu]; exact hHs) hτv hτH
  refine ⟨⟨vote_u, (hCs vote_u).2 (Or.inl ⟨hpw2, ⟨τv, hτv, hτvlt⟩,
    ⟨max τv τH, htau, max_lt hτvlt hτHlt⟩⟩), hidx, hsu, ⟨H_u, hHΦw, hroot, hBH⟩, ?_⟩,
    H_u, hHT2, hBH, τH, hτH, hτHlt⟩
  intro vote' hv' hi'
  obtain ⟨hs', -, hrel⟩ := hRelW vote' hv'
  exact huniq vote' hs' hi' hrel

/-- Lemma 63 read on the voter's pool: each early supporter votes once for `B`'s chain in it. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls). -/
theorem supporters_vote_once_in_pool_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ t_e)
    (h1 : 1 ≤ t_e)
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    (hslot : t_e < slotStart S (s + 1))
    (hhi : t_w + Δ S < slotStart S (s + 2))
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    (hF : (stateBefore x t_w w).S.F.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    ∀ u ∈ Sup,
      VotesOnceInPoolFor (stateBefore x t_w w).A (fg_to_ac (stateBefore x t_w w).S) s B u := by
  obtain ⟨hPer, -⟩ := lem63_supporters_counted_at S Sched x GST s t_e t_f t_w t_v b Sup B v w hDiv
    hMono hSync hCatch hRoots hParent hGST h1 h01 h12 h23 hslot hhi hw hv hSup hF hb
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x t_w w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  have hle12 : stepBefore x t_f ≤ stepBefore x t_w := stepBefore_mono x hDiv h12
  intro u hu
  obtain ⟨vote_u, hpw1, hidx, ⟨τv, hτv, -⟩, ⟨H_u, hHT1, hroot, hBH, hHs, τH, hτH, -⟩,
    huniq⟩ := hPer u hu
  have hpw2 : vote_u ∈ (stateBefore x t_w w).A.pool s := pool_mono x w hle12 s hpw1
  have hsu : vote_u.slot = s := pool_slot_of_stateBefore S Sched x _ w s vote_u hpw1
  have hHT2 : H_u ∈ (stateBefore x t_w w).S.T := mem_T_mono x w hle12 hHT1
  have hHΦw : H_u ∈ (fg_to_ac (stateBefore x t_w w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hHT2, ancestorEq_trans hF hBH⟩
  refine ⟨vote_u, hpw2, hidx,
    ⟨max τv τH, tau_eq_ok_some hRootsΦ hHΦw hroot (by rw [hsu]; exact hHs) hτv hτH⟩,
    ⟨H_u, hHΦw, hroot, hBH⟩, ?_⟩
  intro vote' hv' hi'
  have hsj := pool_slot_of_stateBefore S Sched x _ w s vote' hv'
  obtain ⟨k, hk, hsk, hhk, hlk⟩ :=
    pool_vote_relayed_before S Sched x hMono _ w s vote' hv'
  exact huniq vote' hsj hi' ⟨k, hk, hsk, hhk, by rw [hsj]; exact hlk⟩

/-- Lemma 64, the next slot's Goldfish fork choice extends a block an honest validator finds
eligible, over reading points. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, through `supporters_vote_once_counted_at`, which it calls). -/
theorem lem64_goldfish_vote_extends_eligible_block_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (A' : ACState V) (votes support_votes : Finset (GoldfishVote V))
    (vbt : Finset (Block V)) (H_w : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ t_e)
    (h1 : 1 ≤ t_e)
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    (hslot : t_e < slotStart S (s + 1))
    (hhi : t_w + Δ S < slotStart S (s + 2))
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : voters_count ((stateBefore x t_v v).A.pool s) < 2 * Sup.card)
    (hCounted : CountedVotesAt (stateBefore x t_w w).A (fg_to_ac (stateBefore x t_w w).S)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    (hvbt : ∀ B' : Block V, B' ∈ vbt ↔ VoterTreeAt (stateBefore x t_w w).A
      (fg_to_ac (stateBefore x t_w w).S) ((t_f : ℕ) : Int) (s + 1) B')
    (hWalk : goldfish_fork_choice S.C (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int)
      (get_anchor A' (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int))
      (viable_tree (fg_to_ac (stateBefore x t_w w).S) vbt) votes support_votes s = .ok H_w)
    (hF2 : (fg_to_ac (stateBefore x t_w w).S).fc_root.compatible B = true)
    (hF3 : (fg_to_ac (stateBefore x t_w w).S).fc_root.AncestorEq B →
      ∃ W ∈ vbt, W ∈ (fg_to_ac (stateBefore x t_w w).S).viable_heads ∧ B.AncestorEq W)
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int) e = true →
        e.B.compatible B = true)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    B.AncestorEq H_w := by
  have hFroot : (stateBefore x t_w w).S.F.AncestorEq
      (fg_to_ac (stateBefore x t_w w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x t_w w
  -- the case `B` an ancestor of `w`'s finalized block: the walk's end is the anchor or a
  -- descendant of it, the anchor is `fc_root` or a descendant of it, and `fc_root` is `w`'s
  -- finalized block or a descendant of it
  have hF1 := compatible_of_ancestorEq_compatible hFroot hF2
  rcases (compatible_iff _ _).1 hF1 with hF1 | hBF
  swap
  · have hAH : (get_anchor A' (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int)).AncestorEq
        H_w := by
      rcases GoldilocksCorrectness.Proofs.Routines.ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with hH | ⟨hAH, -⟩
      · rw [hH]
        exact ancestorEq_refl _
      · exact hAH
    exact ancestorEq_trans hBF (ancestorEq_trans hFroot
      (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAH))
  -- the supporters' votes are counted at `w`
  obtain ⟨hPer, hVoters, hSupport⟩ := supporters_vote_once_counted_at S Sched x GST s t_e t_f t_w
    t_v b Sup B v w votes support_votes hDiv hMono hSync hCatch hRoots hParent hGST h1 h01
    h12 h23 hslot hhi hw hv hSup hEligible hF1 hCounted hb
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x t_w w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  obtain ⟨u₀, hu₀⟩ : Sup.Nonempty := Finset.card_pos.1 (by omega)
  -- the start
  obtain ⟨-, H₀, hH₀T, hBH₀, τ₀, hτ₀, hτ₀lt⟩ := hPer u₀ hu₀
  have hAnchor : (get_anchor A' (fg_to_ac (stateBefore x t_w w).S)
      ((t_w : ℕ) : Int)).compatible B = true :=
    GoldilocksCorrectness.Statements.Routines.lem6_get_anchor_compatible A' _ _ B hLocks hF2
  have hStart : StartsTowards (get_anchor A' (fg_to_ac (stateBefore x t_w w).S)
      ((t_w : ℕ) : Int)) B (viable_tree (fg_to_ac (stateBefore x t_w w).S) vbt) := by
    rcases (compatible_iff _ _).1 hF2 with hRoot | hRoot
    · obtain ⟨W, hW, hWv, hRW⟩ := hF3 hRoot
      refine GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible _ vbt _ B
        W hAnchor (fc_root_ancestorEq_get_anchor _ _ _) ?_ ⟨hW, hWv⟩ hRW
      intro P hXP _ hPB
      have hPH : P.AncestorEq H₀ := ancestorEq_trans hPB hBH₀
      have hPT : P ∈ (stateBefore x t_w w).S.T := ancestors_mem_T_of_exec S Sched x _ w _ P hH₀T hPH
      have hFP : (stateBefore x t_w w).S.F.AncestorEq P :=
        ancestorEq_trans hFroot (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hXP)
      have hPΦ : P ∈ (fg_to_ac (stateBefore x t_w w).S).tree := (mem_fg_to_ac_tree _ _).2 ⟨hPT, hFP⟩
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := ancestor_blockStamp_le S Sched x _ w H₀ P hH₀T hPH
      have hτHH : τH = τ₀ := Option.some_injective _ (hτH.symm.trans hτ₀)
      exact (hvbt P).2 ⟨hPΦ, τP, hτP, Or.inl (lt_of_le_of_lt hle (hτHH ▸ hτ₀lt))⟩
    · exact Or.inl (ancestorEq_trans hRoot (fc_root_ancestorEq_get_anchor _ _ _))
  -- the fork choice
  exact GoldilocksCorrectness.Statements.Routines.lem2_goldfish_fork_choice_extends_majority_block
    S.C _ _ votes support_votes s _ B H_w _ Sup hStart hRootsΦ hSupport
    (fun u hu => (hPer u hu).1) hVoters hWalk

end GoldilocksCorrectness.Proofs.Executions
