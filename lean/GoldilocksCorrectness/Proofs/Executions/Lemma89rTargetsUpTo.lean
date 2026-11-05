module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo

@[expose] public section

/-!
# `Lemma89rTargets.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89rTargets.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `round_attestations_in_pool_targets`, `lem80wq_round_height_advances_steps_targets`,
  `lem89r_quiet_round_targets`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_le_of_le
  slot_add_two_le_of_delivery supportCutoff_eq supportCutoff_le_slotStart_succ supportCutoff_mono
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes
  FrameShape lem56_frame_of_shape BoxOne BoxTwo BoxThree frameShape_of_boxOne frameShape_of_boxTwo
  frameShape_of_boxThree lem66_chain_state_certified)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible fc_root_ancestorEq_get_anchor
  ancestorEq_compatible genesis_ancestorEq)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **`round_attestations_in_pool` with the targets premise (a copy).** The hypotheses and the
first conjunct of `round_attestations_in_pool` (`Proofs/Executions/Lemma80.lean`); the second
conjunct reads: when every attestation a member of `Q` put on the wire at a tick at a time
`t' ≤ a`, awake and outside the adversary set at `t'`, at the height `H` of `B`'s chain state, is
a target, then `q`'s pool before `t₁` holds a target of every member of `Q` at `H` naming `T`.

Why: as the original's first conjunct (Lemma 61 at each member, `record_content_sent` for an
attestation already sent), each attestation found being one of the member's, at a tick up to `a`,
at `H`, so a target by the premise.

The variables: as `round_attestations_in_pool`.

Restated with the delivery premises up to `t₁`: each member's attestation, sent by the support cutoff of slot `s + 1` and from `tq` on, reaches `q` one delay later, by `t₁` (`delivered_before_stepBefore_of_honest_send_upTo`), as `round_attestations_in_pool_upTo`. -/
theorem round_attestations_in_pool_targets_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST r s t₁ tq : ℕ) (Q : Finset V) (B : Block V) (q : V)
    (φ : V → Height) (ρ : V → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject t₁)
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject t₁)
    (hs : s = r * S.C.R)
    (hGST : GST ≤ supportCutoff S (s + 1))
    (ht₁ : supportCutoff S (s + 1) + Δ_F S ≤ t₁)
    (hBslot : B.slot = s)
    (hv : ∀ v ∈ Q, ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hUpd : ∀ v ∈ Q, ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧ B ∈ A'.fast_blocks)
    (hLocks : ∀ v ∈ Q, ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hShape : ∀ v ∈ Q, FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S (ρ v) (φ v))
    (hRoot : ∀ v ∈ Q, (ρ v).AncestorEq B)
    (hBin : ∀ v ∈ Q, B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T)
    (hLockBox : ∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root)
    (hBHeight : ∀ v ∈ Q, φ v ≤ (chainStateOf S.C B).h)
    (htq : tq + Δ_F S ≤ t₁)
    (hqAwake : ∀ t : ℕ, tq ≤ t → t ≤ t₁ →
      q ∈ Sched.awake (t : Int) ∧ q ∉ Sched.adv (t : Int)) :
    (∀ u ∈ Q, ∃ a ∈ (stateBefore x t₁ q).S.attestations,
      a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root) ∧
    ((∀ u ∈ Q, ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = AtomicAction.tickAllAwake t' →
        t' ≤ supportCutoff S (s + 1) → u ∈ Sched.awake (t' : Int) → u ∉ Sched.adv (t' : Int) →
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent →
        a.h = (chainStateOf S.C B).h → a.τ = false) →
      ∀ u ∈ Q, ∃ a ∈ (stateBefore x t₁ q).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧
        a.T = (chainStateOf S.C B).T_h.root ∧ a.τ = false) := by
  -- an attestation an honest validator sent by `a` is in `q`'s pool before `t₁`
  have hDeliver : ∀ (j t' : ℕ) (v : V) (a : Attestation V),
      x.lbl j = AtomicAction.tickAllAwake t' → t' ≤ supportCutoff S (s + 1) →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent →
      v ∉ Sched.adv (t' : Int) → a ∈ (stateBefore x t₁ q).S.attestations := by
    intro j t' v a hl ht' hsent hhon
    have hm1 : max t' GST ≤ supportCutoff S (s + 1) := max_le ht' hGST
    have hm2 : max (max t' GST) tq + Δ_F S ≤ t₁ := by
      have := le_max_left (max t' GST) tq
      have := le_max_right (max t' GST) tq
      omega
    obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
    have hhon' : v ∉ Sched.adv (x[j].time : Int) := fun h =>
      hhon (hMono _ _ (by exact_mod_cast (by omega : x[j].time ≤ t')) h)
    obtain ⟨d, -, hld, hd⟩ := delivered_before_stepBefore_of_honest_send_upTo x hDiv
      (hSyncF.mono hm2) (hCatchF.mono hm2)
      hMono (sm := ⟨v, NamedObject.attest a⟩) ⟨hsent, hhon'⟩ trivial
      (le_trans (by omega : x[j + 1].time ≤ t') (le_trans (le_max_left t' GST) (le_max_left _ tq)))
      (le_trans (le_max_right t' GST) (le_max_left _ tq))
      (fun t'' h1 h2 => hqAwake t'' (le_trans (le_max_right _ _) h1) (by omega))
    obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
    have hin : a ∈ (x[d + 1][q].st).S.attestations := by
      rw [hstep]
      exact (on_attestation_pool _ a).2 (tick_attestation_well_formed S Sched x j t' v a hl hsent)
    have hin' : a ∈ (stateBefore x (max (max t' GST) tq + Δ_F S) q).S.attestations :=
      pool_grows_of_le x q hd a hin
    exact pool_grows_of_le x q (stepBefore_mono x hDiv hm2) a hin'
  have hDuty : ∀ v ∈ Q, dutyWindowStart S (s + 1) ≤ supportCutoff S (s + 1) := by
    intro v _
    have hΔ := one_le_Δ S
    have h1 := dutyWindowStart_succ_le_slotStart S s
    have h2 : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    rw [supportCutoff_eq, voteTime_eq]
    omega
  refine ⟨fun u hu => ?_, fun hTgt u hu => ?_⟩
  · obtain ⟨A', hU, hS, hF⟩ := hUpd u hu
    have hLk := update_lock_entries_ancestorEq S Sched x s B u A' hDiv hMono (hv u hu) hU
      hS hBslot (hLocks u hu)
    rcases lem61_honest_validator_attests_frame S Sched x r s B u A' (ρ u) (φ u) hDiv hMono
        hs (hv u hu) hU hS hF hLk (hShape u hu) (hRoot u hu) (hBHeight u hu) (hBin u hu)
        (hLockBox u hu)
      with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
    · exact ⟨a, hDeliver i _ u a hl le_rfl hsent (hv u hu _ (hDuty u hu) le_rfl).2, hav, hah, haT⟩
    · obtain ⟨j, t', a, hl, ht', -, hadv, hsent, hav, hac, -⟩ :=
        record_content_sent S Sched x _ u b hDiv hb
      refine ⟨a, hDeliver j t' u a hl ht'.le hsent hadv, hav, ?_, ?_⟩
      · rw [← hbh, ← hac]
        rfl
      · rw [← hbT, ← hac]
        rfl
  · obtain ⟨A', hU, hS, hF⟩ := hUpd u hu
    have hLk := update_lock_entries_ancestorEq S Sched x s B u A' hDiv hMono (hv u hu) hU
      hS hBslot (hLocks u hu)
    rcases lem61_honest_validator_attests_frame S Sched x r s B u A' (ρ u) (φ u) hDiv hMono
        hs (hv u hu) hU hS hF hLk (hShape u hu) (hRoot u hu) (hBHeight u hu) (hBin u hu)
        (hLockBox u hu)
      with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
    · have hw := hv u hu _ (hDuty u hu) le_rfl
      exact ⟨a, hDeliver i _ u a hl le_rfl hsent hw.2, hav, hah, haT,
        hTgt u hu i _ a hl le_rfl hw.1 hw.2 hsent hah⟩
    · obtain ⟨j, t', a, hl, ht', hawk, hadv, hsent, hav, hac, -⟩ :=
        record_content_sent S Sched x _ u b hDiv hb
      have hah : a.h = (chainStateOf S.C B).h := by
        rw [← hbh, ← hac]
        rfl
      refine ⟨a, hDeliver j t' u a hl ht'.le hsent hadv, hav, hah, ?_,
        hTgt u hu j t' a hl ht'.le hawk hadv hsent hah⟩
      rw [← hbT, ← hac]
      rfl

/-- **`lem80wq_round_height_advances_steps` with the targets premise (a copy).** The hypotheses
and the first two conjuncts of `lem80wq_round_height_advances_steps`
(`Proofs/Executions/Lemma80.lean`); the third reads: when every attestation a member of `Q` put on
the wire at a tick at a time `t' ≤ a`, awake and outside the adversary set at `t'`, at the height
`H` of `B`'s chain state, is a target, then `B'`'s chain state is at least one height above `B`'s,
and, when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`.

Why: the original's proof, with `round_attestations_in_pool_targets` for the pool's targets.

The variables: as `lem80wq_round_height_advances_steps`.

Roots name blocks until `supportCutoff S (s'' - 1)`: as `lem80wq_round_height_advances_steps`:
the base at slot `s`, the round's chain steps, and the next proposal at slot `s'' − 1` read
blocks held up to the support cutoff of slot `s'' − 1`.

Restated with the delivery premises up to `supportCutoff S (s'' - 1)`, the attestations' up to `slotStart S s''`: the blocks and Goldfish votes the proof reads are due by the support cutoff of slot `s'' − 1` (`round_proposal_extends_upTo`), the attestations by the start of slot `s''` (`round_attestations_in_pool_targets_upTo`), as `lem80wq_round_height_advances_steps_upTo`. -/
theorem lem80wq_round_height_advances_steps_targets_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s'' - 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s'' - 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S s''))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S s''))
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape (stateBefore x (slotStart S s) p).S ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape (stateBefore x (voteTime S s) w).S (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = AtomicAction.tickAllAwake t' →
        t' ≤ supportCutoff S (s + 1) → u ∈ Sched.awake (t' : Int) → u ∉ Sched.adv (t' : Int) →
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent →
        a.h = (chainStateOf S.C B).h → a.τ = false) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) := by
  -- the slots: `s'' = s₂ + 2`, with `s ≤ s₂`
  have hR := S.C.R_ge_two
  have hs2 := slot_add_two_le_of_delivery S hs''
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  rw [show s₂ + 2 - 1 = s₂ + 1 by omega] at hVotersQ hStepLast hq
  -- the times
  have hΔ := one_le_Δ S
  have hss : ∀ k, slotStart S (k + 1) = slotStart S k + 4 * Δ S := fun k => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv : ∀ k, voteTime S k = slotStart S k + Δ S := voteTime_eq S
  have hc : ∀ k, supportCutoff S k = voteTime S k + Δ S := supportCutoff_eq S
  have hsm : s - 1 + 1 = s := by omega
  have hvs0 := hv (s - 1)
  have hss0 : slotStart S s = slotStart S (s - 1) + 4 * Δ S := by rw [← hss (s - 1), hsm]
  have hvs := hv s
  have hss1 := hss s
  have hvs1 := hv (s + 1)
  have hcs1 := hc (s + 1)
  have hm2 := slotStart_le_of_le S (show s + 2 ≤ s₂ + 2 by omega)
  have hss2 : slotStart S (s + 2) = slotStart S (s + 1) + 4 * Δ S := hss (s + 1)
  have ha : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S (s₂ + 2) := hs''
  have hdw₁ : dutyWindowStart S s ≤ dutyWindowStart S (s + 1) := dutyWindowStart_mono S (by omega)
  have hdwS : dutyWindowStart S s ≤ slotStart S (s - 1) := by
    have h := dutyWindowStart_succ_le_slotStart S (s - 1)
    rw [hsm] at h
    exact h
  have hc2' : supportCutoff S (s₂ + 1 + 1) = voteTime S (s₂ + 1 + 1) + Δ S := hc _
  have hv2' : voteTime S (s₂ + 1 + 1) = slotStart S (s₂ + 1 + 1) + Δ S := hv _
  have hss2' : slotStart S (s₂ + 1 + 1) = slotStart S (s₂ + 2) := rfl
  -- `B` is of slot `s`
  have hPropose₀ : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s - 1 + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent := by
    rw [hsm]
    exact hPropose
  obtain ⟨i₀, hl₀, hsent₀⟩ := hPropose₀
  have hBslot : B.slot = s := by
    rw [← hsm]
    exact (proposal_parent_walk_end S Sched x (s - 1) i₀ B p hl₀ hsent₀).1
  -- step 1: the base, at the first slot's set
  obtain ⟨hHeld, hBase, hUpd⟩ := round_base_steps_upTo S Sched x GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p φ φw φv ρp ρw ρv hDiv hMono (hSync.mono (supportCutoff_mono S (by omega)))
    (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hs1 hGST
    (fun v hv' t h1 h2 => hHon s le_rfl (by omega) v hv' t h1 h2 (by omega)) hp hPropose hHsPrev
    hVotersPrev hApX hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf hShapeP hShapeW hShapeV hFloorW
    hRootW hRootAr hHeadP
  -- step 2: the invariant through the round, from one slot's set to the next
  obtain ⟨hInv, hVotes⟩ := round_honestChainExtends_steps_upTo S Sched x GST s s₂ Hon Hs B hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner (by omega)
    (by omega) hHonMono hHon hHs hVoters hStep
    hStepLast hBase
  -- the next proposer is awake and honest from the duty window's start of slot `s` to `t_{s''}`
  have hqWin : ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S (s₂ + 2) →
      q ∈ Sched.awake (t : Int) ∧ q ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hd : s + (s₂ + 1 - s) = s₂ + 1 := by omega
    have hsc := supportCutoff_le_slotStart_succ S (s₂ + 2)
    have hc2 : supportCutoff S (s₂ + 2) = voteTime S (s₂ + 2) + Δ S := hc (s₂ + 2)
    have hv2 : voteTime S (s₂ + 2) = slotStart S (s₂ + 2) + Δ S := hv (s₂ + 2)
    refine members_window_of_sets S Sched s (s₂ + 2) Hon hHonMono hHon (s₂ + 1 - s) (by omega) q
      (by rw [hd]; exact hq) t h1 (by rw [hd]; omega) h2
  -- step 3: the attestations in `q`'s pool
  obtain ⟨hPool, hPoolT⟩ := round_attestations_in_pool_targets_upTo S Sched x GST r s (slotStart S (s₂ + 2))
    (dutyWindowStart S s) Q B q φv ρv hDiv hMono hSyncF hCatchF hs (by omega) ha hBslot
    (fun v hv' t h1 h2 => hHon s le_rfl (by omega) v (hQ hv') t (by omega) h2 (by omega))
    (fun v hv' => hUpd v (hQ hv')) (fun v hv' => hBase.2.1 v (hQ hv'))
    (fun v hv' => hShapeV v (hQ hv')) (fun v hv' => hRootAr v (hQ hv'))
    (fun v hv' => (stateBefore_grows x hDiv v (by omega)).1 (hHeld v (hQ hv'))) hLockBox
    (fun v hv' => hFloorV v (hQ hv')) (by omega) hqWin
  -- step 4: `q`'s proposal is on `B`'s chain
  have hss₂ : slotStart S (s₂ + 2) = slotStart S (s₂ + 1) + 4 * Δ S := hss (s₂ + 1)
  have hss₃ := hss s₂
  have hdw₂ : dutyWindowStart S (s₂ + 1) ≤ slotStart S s₂ := dutyWindowStart_succ_le_slotStart S s₂
  have hsc₂ := supportCutoff_le_slotStart_succ S (s₂ + 2)
  have hc₂ : supportCutoff S (s₂ + 2) = voteTime S (s₂ + 2) + Δ S := hc (s₂ + 2)
  have hv₂ : voteTime S (s₂ + 2) = slotStart S (s₂ + 2) + Δ S := hv (s₂ + 2)
  have hm3 := slotStart_le_of_le S (show s ≤ s₂ by omega)
  have hBB'p := round_proposal_extends_upTo S Sched x GST s₂ (Hon (s₂ + 1)) (Hs (s₂ + 1)) B B' q
    hDiv hMono (hSync.mono (supportCutoff_mono S (by omega)))
    (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner
    (by rw [hv (s₂ + 1)]; omega)
    (honestChainExtends_mono S Sched x (Hon s₂) (Hon (s₂ + 1)) B s₂
      (hHonMono s₂ (by omega) (by omega)) hInv) hVotes hq
    (fun t h1 h2 => hHon (s₂ + 1) (by omega) (by omega) q hq t h1 (by omega) h2)
    (hHs (s₂ + 1) (by omega) (by omega))
    (fun u hu => (hHon (s₂ + 1) (by omega) (by omega) u hu _ (by omega) (by omega) le_rfl).2)
    hVotersQ hFrameQ hPropose'
  obtain ⟨i', hl', hsent'⟩ := id hPropose'
  obtain ⟨-, -, hB'par?, -⟩ := proposal_parent_walk_end S Sched x (s₂ + 1) i' B' q hl' hsent'
  have hB'p : B'.parent.AncestorEq B' := ancestorEq_of_parent? hB'par?
  have hBB' := ancestorEq_trans hBB'p hB'p
  -- step 5: the certificate
  have hd1 := (lem47_chain_state_heights S.C B B'.parent).2.2.2.1 hBB'p
  have hd2 := (lem47_chain_state_heights S.C B'.parent B').2.2.2.1 hB'p
  by_cases heq : (chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h
  · have hT : (chainStateOf S.C B'.parent).T_h = (chainStateOf S.C B).T_h :=
      ((lem47_chain_state_heights S.C B B'.parent).2.2.2.2 hBB'p heq.symm).symm
    have hPool' : ∀ u ∈ Q, ∃ a ∈ (stateBefore x (slotStart S (s₂ + 2)) q).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C B'.parent).h ∧
        a.T = (chainStateOf S.C B'.parent).T_h.root := by
      rw [heq, hT]
      exact hPool
    obtain ⟨h53a, h53b⟩ := lem53_next_honest_proposal_carries_certificate S Sched x (s₂ + 2) q B'
      B'.parent Q hPropose' rfl hQuorum hPool'
    rw [heq, hT] at h53a h53b
    refine ⟨hBB', ?_, fun hTgt => ?_⟩
    · rcases h53a with h | h
      · exact Or.inl (by unfold Height at *; omega)
      · exact Or.inr h
    · obtain ⟨h1, h2⟩ := h53b (hPoolT hTgt)
      exact ⟨by unfold Height at *; omega, fun _ => h2⟩
  · have hlt : (chainStateOf S.C B).h < (chainStateOf S.C B'.parent).h := by
      unfold Height at *
      omega
    have hge : (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h := by
      unfold Height at *
      omega
    exact ⟨hBB', Or.inl hge, fun _ => ⟨hge, fun h => absurd h heq⟩⟩

/-- **`lem89r_quiet_round` with the targets premise (a copy).** The hypotheses and the conclusion
of `lem89r_quiet_round` (`Statements/Executions/Lemma89rStatements.lean`) but its third conjunct,
which reads: when every attestation a member of `Hon s` put on the wire at a tick at a time
`t' ≤ supportCutoff S (s + 1)`, awake and outside the adversary set at `t'`, at the height of
`B`'s chain state, is a target, then `B'`'s chain state is at least one height above `B`'s, and,
when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`.

Why: the original's proof, with `lem80wq_round_height_advances_steps_targets` for the round
theorem.

The variables: as `lem89r_quiet_round`.

Read aloud: in a quiet round of the phase, when every member's attestation at the proposal's height
is a target, the next honest proposal is one height higher and, when its parent is at the
proposal's height, justifies the proposal's entry.

Roots name blocks until `supportCutoff S (s'' - 1)`: as `lem89r_quiet_round`: the round theorem
at slot `s''` reads blocks held up to it, and the chain steps of the slots before `s'' − 1` up
to their support cutoffs, at most it.

Restated with the delivery premises up to `supportCutoff S (s'' - 1)`: the bound of its roots, for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to `slotStart S s''`, the bound `lem80wq_round_height_advances_steps_targets_upTo` reads them at, as `lem89r_quiet_round_upTo`. -/
theorem lem89r_quiet_round_targets_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST r s s'' : ℕ) (Hon : ℕ → Finset V)
    (𝓒 : Block V → Prop) (B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s'' - 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s'' - 1)))
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S s''))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S s''))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    (hGST : GST ≤ voteTime S (s - 1))
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) ((supportCutoff S (s + 1) : ℕ) : Int))
    (hHonMono : ∀ s', s - 1 ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    (hHon : ∀ s', s - 1 ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hQuorum : quorum V ≤ (Hon s).card)
    (hCommittees : ∀ s', s - 1 ≤ s' → s' < s'' →
      (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon s').card)
    (hpAwake : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s → p ∈ Sched.awake (t : Int))
    (hpHon : HonestThroughTime Sched ((voteTime S s : ℕ) : Int) p)
    (hq : q ∈ Hon (s'' - 1)) (hps : S.P.proposer s = p) (hqProp : S.P.proposer s'' = q)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hQuiet : QuietRoundOnConfirmations S Sched x Hon B s s'')
    (hChain : ChainInvFor S Sched x (Hon (s - 1)) 𝓒 (s - 1))
    (hFamLocks : ∀ w ∈ Hon (s - 1), LiveLocksOnFamilyAt S Sched x 𝓒 (s - 1) w)
    (hAnchor : 𝓒 (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)))
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S s) p).S).viable_heads ∧ C.AncestorEq W) :
    (∃ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root = B.root) ∨
    (B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (chainStateOf S.C B').progress)) ∧
    ((∀ u ∈ Hon s, ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = AtomicAction.tickAllAwake t' →
        t' ≤ supportCutoff S (s + 1) → u ∈ Sched.awake (t' : Int) → u ∉ Sched.adv (t' : Int) →
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent →
        a.h = (chainStateOf S.C B).h → a.τ = false) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) ∧
    (∀ v ∈ Hon s,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B) ∧
    ChainInvFor S Sched x (Hon (s'' - 1)) (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C)
      (s'' - 1) ∧
    (∀ w ∈ Hon (s'' - 1), LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C)
      (s'' - 1) w)) := by
  -- the collision case
  by_cases hColl : ∃ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root = B.root
  · exact Or.inl hColl
  right
  have hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root :=
    fun B₁ hB₁ he => hColl ⟨B₁, hB₁, he⟩
  -- the slots: `s = s₀ + 1`, `s'' = s₂ + 2`
  have hR := S.C.R_ge_two
  have hs2 := slot_add_two_le_of_delivery S hs''
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hGST hHonMono hHon hCommittees hpAwake hChain hFamLocks ⊢
  simp only [show s₂ + 2 - 1 = s₂ + 1 by omega] at hq ⊢
  -- the clause of the quiet round relative to the confirmations, at the slots `s₀` to `s₂`
  have hQ4 : ∀ s', s₀ ≤ s' → s' ≤ s₂ → ∀ σ, s₀ ≤ σ → σ ≤ s' → ∀ v ∈ Hon σ,
      ∀ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
      ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x C s' w :=
    fun s' h1 h2 σ h3 h4 => hQuiet.2.2.2.1 s' (by omega) (by omega) σ (by omega) h4
  -- the times
  have hΔ := one_le_Δ S
  have hss : ∀ k, slotStart S (k + 1) = slotStart S k + 4 * Δ S := fun k => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv : ∀ k, voteTime S k = slotStart S k + Δ S := voteTime_eq S
  have hc : ∀ k, supportCutoff S k = voteTime S k + Δ S := supportCutoff_eq S
  have hdw : ∀ k, dutyWindowStart S (k + 1) ≤ slotStart S k := dutyWindowStart_succ_le_slotStart S
  have hdwm : ∀ a b : ℕ, a ≤ b → dutyWindowStart S a ≤ dutyWindowStart S b :=
    fun a b h => dutyWindowStart_mono S h
  have hscm : ∀ a b : ℕ, a ≤ b → supportCutoff S a ≤ supportCutoff S b := by
    intro a b h
    have := slotStart_le_of_le S h
    rw [hc, hc, hv, hv]
    omega
  have hdwv : ∀ k, dutyWindowStart S k ≤ voteTime S k := by
    intro k
    have h1 := hdwm k (k + 1) (by omega)
    have h2 := hdw k
    have h3 := hv k
    omega
  have hvc : ∀ k, voteTime S k ≤ supportCutoff S (k + 1) := by
    intro k
    have h1 := hc (k + 1)
    have h2 := hv (k + 1)
    have h3 := hv k
    have h4 := hss k
    omega
  have hThirdAt : ∀ t : ℕ, t ≤ supportCutoff S (s₀ + 1 + 1) →
      AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int) :=
    fun t ht => adversaryFewerThanThirdUntil_of_le (by exact_mod_cast ht) hThird
  -- the voters of each slot: the committee members in the slot's set, each of whom votes
  set Hs : ℕ → Finset V := fun s' => S.P.committee s' ∩ Hon s' with hHsDef
  have hVotes : ∀ s', s₀ ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent := by
    intro s' h1 h2 u hu
    obtain ⟨hk, huH⟩ := Finset.mem_inter.1 hu
    have hd := hdwv s'
    have hvc' := hvc s'
    obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ := honest_votes_of_window S Sched x s' u hDiv hMono
      (fun t h1' h2' => (hHon s' h1 h2 u huH t h1' (by omega)).1)
      (hHon s' h1 h2 u huH _ hd hvc').2 hk
    exact ⟨huH, hk, vote, hvi, hvs, i, hl, hsent⟩
  have hCnt := fun s' (h1 : s₀ ≤ s') (h2 : s' < s₂ + 2) (t : ℕ) (v : V) =>
    counting_of_committee_majority S Sched x s' t (Hon s') v (hCommittees s' h1 h2)
  -- the proposer
  have hp' : ∀ t : ℕ, voteTime S s₀ ≤ t → t ≤ slotStart S (s₀ + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have h3 := hv (s₀ + 1)
    exact ⟨hpAwake t h1 h2, hpHon (t : Int) (by exact_mod_cast (by omega : t ≤ voteTime S (s₀ + 1)))⟩
  obtain ⟨iB, hlB, hsentB⟩ := id hPropose
  obtain ⟨hBslot, -, hBpar?, -⟩ := proposal_parent_walk_end S Sched x s₀ iB B p hlB hsentB
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  -- every block of the family is `B`'s parent or an ancestor of it
  have hFamPar : ∀ C : Block V, 𝓒 C → C.AncestorEq B.parent := by
    refine family_ancestorEq_proposal_parent_upTo S Sched x GST s₀ (Hs s₀) 𝓒 B p hDiv hMono
      (hSync.mono (hscm _ _ (by omega)))
      (hCatch.mono (hscm _ _ (by omega)))
      (hRoots.mono (hscm _ _ (by omega))) hParent hOwner hGST ?_ ?_ ?_ ?_ hPropose
      hFrameP hAnchor
    · intro u hu
      obtain ⟨huH, hk, vote, -, -, i, hl, hsent⟩ := hVotes s₀ le_rfl (by omega) u hu
      have h1 := hss s₀
      have h2 := hc (s₀ + 1)
      have h3 := hv (s₀ + 1)
      have h4 := hdwv s₀
      have h5 := hv s₀
      exact ⟨hk, (hHon s₀ le_rfl (by omega) u huH (slotStart S (s₀ + 1)) (by omega)
        (by omega)).2, vote, i, hl, hsent⟩
    · intro C hC u hu vote hsend
      exact (hChain C hC).1 u (Finset.mem_inter.1 hu).2 vote hsend
    · exact (hCnt s₀ le_rfl (by omega) (slotStart S (s₀ + 1)) p).2.1
    · intro t h1 h2
      have h3 := supportCutoff_le_slotStart_succ S s₀
      exact hp' t h1 (by omega)
  -- the anchor and the votes of slot `s₀`
  set anchor := get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
    (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S) ((slotStart S (s₀ + 1) : ℕ) : Int)
    with hanchor
  have hex : ∀ u ∈ Hs s₀, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧ anchor.AncestorEq H_u := by
    intro u hu
    obtain ⟨huH, -, vote, -, -, i, hl, hsent⟩ := hVotes s₀ le_rfl (by omega) u hu
    obtain ⟨H_u, hT, hvt, hAH⟩ := (hChain anchor hAnchor).1 u huH vote ⟨i, hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i, hl, hsent⟩, hT, hAH⟩
  choose Hc hHc using hex
  let H : V → Block V := fun u => if h : u ∈ Hs s₀ then Hc u h else B
  have hH : ∀ u (hu : u ∈ Hs s₀), H u = Hc u hu := fun u hu => dif_pos hu
  have hHsPrev : ∀ u ∈ Hs s₀, u ∈ S.P.committee s₀ ∧
      u ∉ Sched.adv (voteTime S (s₀ + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧ anchor.AncestorEq (H u) := by
    intro u hu
    obtain ⟨huH, hk, -⟩ := hVotes s₀ le_rfl (by omega) u hu
    have h1 := hc (s₀ + 1)
    have h2 := hdwv s₀
    have h3 := hvc s₀
    have h4 := hv (s₀ + 1)
    have h5 := hss s₀
    have h6 := hv s₀
    rw [hH u hu]
    exact ⟨hk, (hHon s₀ le_rfl (by omega) u huH (voteTime S (s₀ + 1)) (by omega)
      (by omega)).2, (hHc u hu).1,
      (hHc u hu).2.1, (hHc u hu).2.2⟩
  have hVotersPrev : ∀ w ∈ Hon (s₀ + 1), ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s₀ + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S) (s₀ + 1) votes support_votes →
      voters_count votes < 2 * (Hs s₀).card :=
    fun w _ => (hCnt s₀ le_rfl (by omega) (voteTime S (s₀ + 1)) w).2.2
  -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
  have hLocksW : ∀ w ∈ Hon (s₀ + 1), ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1)) w).A
        ((voteTime S (s₀ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
        ((voteTime S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
          ((voteTime S (s₀ + 1) : ℕ) : Int) e = true → e.B.AncestorEq B.parent := by
    intro w hw A' hR e he hl
    obtain ⟨D, hD, heD⟩ := hFamLocks w (hHonMono s₀ le_rfl (by omega) hw) A' hR e he hl
    exact ancestorEq_trans heD (hFamPar D hD)
  have hOnly : ∀ w ∈ Hon (s₀ + 1), ∀ B₁ ∈ (stateBefore x (voteTime S (s₀ + 1)) w).S.T,
      B₁.slot = s₀ + 1 → B₁ = B :=
    fun w _ B₁ hB₁ hslot => only_block_of_unforgeability S Sched x hU (s₀ + 1)
      (voteTime S (s₀ + 1)) B B₁ p w hpHon hps hPropose hB₁ hslot
  -- the frames at the three reading points
  have hFloorW : ∀ w ∈ Hon (s₀ + 1),
      head_height_floor (stateBefore x (slotStart S (s₀ + 1)) p).S ≤
        head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ∧
      head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
        (chainStateOf S.C B.parent).h := by
    intro w hw
    refine ⟨?_, (hQuiet.1 w hw).2⟩
    have h1 := hv (s₀ + 1)
    have h2 := hdw s₀
    have h3 := hss s₀
    have h4 := hvc (s₀ + 1)
    have h6 := hv s₀
    have hvR : slotStart S (s₀ + 1) + Δ S ≤ supportCutoff S (s₀ + 1 + 1) := by omega
    have hfl := floor_le_of_delivery_unordered_upTo S Sched x GST (slotStart S (s₀ + 1)) p w hDiv hMono
      (hSync.mono (le_trans hvR (hscm _ _ (by omega))))
      (hCatch.mono (le_trans hvR (hscm _ _ (by omega))))
      (hRoots.mono (le_trans hvR (hscm _ _ (by omega)))) hParent hU
      (hThirdAt _ (by omega)) (by omega)
      (hp' _ (by omega) le_rfl).2
      (fun t' h1' h2' => hHon (s₀ + 1) (by omega) (by omega) w hw t' (by omega) (by omega))
    rw [← hv (s₀ + 1)] at hfl
    exact hfl
  have hHeadP := anchor_has_viable_head S Sched x (slotStart S (s₀ + 1)) p
    (stateBefore x (slotStart S (s₀ + 1)) p).A ((slotStart S (s₀ + 1) : ℕ) : Int)
  -- the windows and counts as the round theorem reads them
  have hHonMono' : ∀ s', s₀ + 1 ≤ s' → s' + 1 < s₂ + 2 → Hon (s' + 1) ⊆ Hon s' :=
    fun s' h1 h2 => hHonMono s' (by omega) h2
  have hHon' : ∀ s', s₀ + 1 ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S (s₂ + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun s' h1 h2 v hv' t ht1 ht2 _ => hHon s' (by omega) h2 v hv' t ht1 ht2
  have hHs' : ∀ s', s₀ + 1 ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧
      u ∈ S.P.committee s' ∧ ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent :=
    fun s' h1 h2 => hVotes s' (by omega) h2
  have hVoters' : ∀ s', s₀ + 1 ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card :=
    fun s' h1 h2 v _ => ⟨(hCnt s' (by omega) h2 (voteTime S (s' + 1)) v).2.2,
      (hCnt s' (by omega) h2 (supportCutoff S (s' + 1)) v).2.1⟩
  have hStep : ∀ s', s₀ + 1 ≤ s' → s' + 3 ≤ s₂ + 2 → ∀ w ∈ Hon (s' + 1),
      StepFrameAt S Sched x B s' w :=
    fun s' h1 h2 w hw => hQuiet.2.2.1 s' h1 (by omega) w hw
  have hStepLast := fun w (hw : w ∈ Hon (s₂ + 1)) =>
    And.intro (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).1 (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).2.1
  have hLockBox : ∀ v ∈ Hon (s₀ + 1),
      (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root :=
    fun v hv' => lockBox_of_frame S Sched x hU _ v B (hThirdAt _ le_rfl)
      (hQuiet.2.1 v hv').1 (hQuiet.2.1 v hv').2
  -- the base of the round
  obtain ⟨hHeld, hBase, hUpd⟩ := round_base_steps_upTo S Sched x GST (s₀ + 1) (Hon (s₀ + 1))
    (Hs (s₀ + 1)) (Hs s₀) H anchor B p _
    (fun w => head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    (get_fc_root (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    hDiv hMono (hSync.mono (hscm _ _ (by omega))) (hCatch.mono (hscm _ _ (by omega)))
    (hRoots.mono (hscm _ _ (by omega))) hParent hOwner (by omega)
    hGST
    (fun v hv' t h1 h2 => hHon (s₀ + 1) (by omega) (by omega) v hv' t h1 h2) hp' hPropose hHsPrev
    hVotersPrev (ancestorEq_refl _) hLocksW hOnly hRootNew (hHs' (s₀ + 1) le_rfl (by omega))
    (fun v hv' => (hVoters' (s₀ + 1) le_rfl (by omega) v hv').2)
    (hCnt (s₀ + 1) (by omega) (by omega) 0 p).1 ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) hFloorW (fun w hw => (hQuiet.1 w hw).1)
    (fun v hv' => (hQuiet.2.1 v hv').1) hHeadP
  -- the chain invariant relative to `B` at the slots `s₂` and `s₂ + 1`
  have hg1 := hv s₀
  have hg2 := hss s₀
  have hg3 := hv (s₀ + 1)
  have hg4 := hv s₂
  have hg5 := slotStart_le_of_le S (show s₀ ≤ s₂ by omega)
  have hGST₁ : GST ≤ voteTime S (s₀ + 1) := by omega
  have hGST₂ : GST ≤ voteTime S s₂ := by omega
  obtain ⟨hInv, -⟩ := round_honestChainExtends_steps_upTo S Sched x GST (s₀ + 1) s₂ Hon Hs B hDiv
    hMono (hSync.mono (hscm _ _ (by omega))) (hCatch.mono (hscm _ _ (by omega)))
    (hRoots.mono (hscm _ _ (by omega))) hParent hOwner hGST₁ (by omega)
    hHonMono' hHon' hHs'
    hVoters' hStep hStepLast hBase
  have hInv' := lem79_step_sets_upTo S Sched x GST s₂ (Hon s₂) (Hon (s₂ + 1)) Hs B hDiv hMono
    (hSync.mono (hscm _ _ (by omega)))
    (hCatch.mono (hscm _ _ (by omega)))
    (hRoots.mono (hscm _ _ (by omega))) hParent hOwner hGST₂ hInv
    (hHonMono s₂ (by omega) (by omega))
    (fun v hv' t ht1 ht2 => hHon s₂ (by omega) (by omega) v hv' t ht1 ht2)
    (fun v hv' t ht1 ht2 => hHon (s₂ + 1) (by omega) (by omega) v hv' t ht1 ht2)
    (hVotes s₂ (by omega) (by omega)) (hVotes (s₂ + 1) (by omega) (by omega))
    (fun w _ => (hCnt s₂ (by omega) (by omega) (voteTime S (s₂ + 1)) w).2.2)
    (fun v _ => (hCnt (s₂ + 1) (by omega) (by omega) (supportCutoff S (s₂ + 2)) v).2.1)
    (fun w hw => (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).1)
    (fun w hw => (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).2.1)
    (fun w hw => (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).2.2)
  -- the next proposer's frame on `B`'s chain, from the proposer clause and the chain invariant
  -- relative to `B` at slot `s₂`
  have hChainB : ∀ C : Block V, (∃ v ∈ Hon s₂,
      (stateBefore x (supportCutoff S (s₂ + 1) + 1) v).A.saved_confirmation s₂ = some C) →
      B.AncestorEq C := by
    rintro C ⟨v, hv', hC⟩
    exact hInv.2.2 v hv' C hC
  have hFrameQ := frameQ_of_quietRoundOnConfirmations S Sched x Hon B (s₀ + 1) (s₂ + 2) hQuiet
    hChainB
  rw [hqProp] at hFrameQ
  -- the round theorem
  obtain ⟨h80a, h80b, h80c⟩ :=
    lem80wq_round_height_advances_steps_targets_upTo S Sched x GST r
    (s₀ + 1) (s₂ + 2) Hon (Hon (s₀ + 1)) Hs H anchor B B' p q _
    (fun w => head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    (get_fc_root (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST
    hHonMono' hHon' hp' hPropose hHsPrev hVotersPrev (ancestorEq_refl _) hLocksW hOnly hRootNew
    hHs' hVoters'
    (fun votes sv hP => by
      rw [hP.1]
      exact (hCnt (s₂ + 1) (by omega) (by omega) (slotStart S (s₂ + 2)) q).2.1)
    (hCnt (s₀ + 1) (by omega) (by omega) 0 p).1 ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) hFloorW (fun v hv' => (hQuiet.2.1 v hv').2)
    (fun w hw => (hQuiet.1 w hw).1) (fun v hv' => (hQuiet.2.1 v hv').1) hHeadP hStep hStepLast
    (Finset.Subset.refl _) hQuorum hLockBox hq hFrameQ hPropose'
  -- the frame of every member of `Hon s` at slot `s₀` relative to `B`
  have hStepB₀ : ∀ w ∈ Hon (s₀ + 1), StepFrameAt S Sched x B s₀ w := fun w hw =>
    stepFrameAt_proposal_of_quiet S Sched x B s₀ w hBslot (hHeld w hw)
      (ancestorEq_trans (hQuiet.1 w hw).1 hPB)
      (le_trans (hQuiet.1 w hw).2 (chainStateOf_height_mono S.C hPB)) (hQuiet.2.1 w hw).1
  -- both invariants carried by the chain step `lem89s_chain_step_upTo` (the voters `Hon σ`, the members
  -- `Hon (σ + 1)`, the updaters `Hon σ`) and the lock invariant's step from slot `s₀` to slot
  -- `s₀ + n`, for `𝓒` and the ancestors of the confirmations of the slots from `s₀` to
  -- `s₀ + n − 1` saved by the members of each slot's own set
  have hIter : ∀ n, s₀ + n ≤ s₂ + 1 →
      ChainInvFor S Sched x (Hon (s₀ + n)) (fun C => 𝓒 C ∨ ∃ σ, s₀ ≤ σ ∧ σ < s₀ + n ∧
        ∃ v ∈ Hon σ, ∃ C' : Block V,
          (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
          C.AncestorEq C') (s₀ + n) ∧
      ∀ u ∈ Hon (s₀ + n), LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ ∃ σ, s₀ ≤ σ ∧
        σ < s₀ + n ∧ ∃ v ∈ Hon σ, ∃ C' : Block V,
          (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
          C.AncestorEq C') (s₀ + n) u := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · intro C hC
        rcases hC with hC | ⟨σ, h1, h2, -⟩
        · exact hChain C hC
        · omega
      · intro u hu A' hR' e he hl
        obtain ⟨D, hD, heD⟩ := hFamLocks u hu A' hR' e he hl
        exact ⟨D, Or.inl hD, heD⟩
    | succ n ih =>
      intro hn
      obtain ⟨hI, hL⟩ := ih (by omega)
      have hGSTn : GST ≤ voteTime S (s₀ + n) := by
        have h1 := slotStart_le_of_le S (show s₀ ≤ s₀ + n by omega)
        have h2 := hv (s₀ + n)
        omega
      -- the three sets of the chain step: the voters `Hon (s₀ + n)`, the members
      -- `Hon (s₀ + n + 1)`, the updaters `Hon (s₀ + n)`
      have hcN : supportCutoff S (s₀ + n + 1 + 1) = voteTime S (s₀ + n + 2) + Δ S :=
        supportCutoff_eq S _
      have hd0 : dutyWindowStart S (s₀ + n) ≤ supportCutoff S (s₀ + n + 1) :=
        dutyWindowStart_le_supportCutoff S (by omega)
      have hd1 : dutyWindowStart S (s₀ + n + 1) ≤ supportCutoff S (s₀ + n + 1) :=
        dutyWindowStart_le_supportCutoff S (by omega)
      have hd2 : dutyWindowStart S (s₀ + n + 1) ≤ supportCutoff S (s₀ + n + 1 + 1) :=
        dutyWindowStart_le_supportCutoff S (by omega)
      have hdd : dutyWindowStart S (s₀ + n) ≤ dutyWindowStart S (s₀ + n + 1) :=
        hdwm (s₀ + n) (s₀ + n + 1) (by omega)
      have hHonN := fun v hv' t ht1 ht2 => hHon (s₀ + n) (by omega) (by omega) v hv' t ht1 ht2
      have hHonN' := fun v hv' t ht1 ht2 =>
        hHon (s₀ + n + 1) (by omega) (by omega) v hv' t ht1 ht2
      have hHonA : Hon (s₀ + n) ⊆ honestActiveAt S Sched (s₀ + n) := by
        intro u hu
        unfold honestActiveAt activeAt
        rw [Finset.mem_sdiff]
        exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHonN u hu t h1 h2).1),
          (hHonN u hu _ hd0 le_rfl).2⟩
      have hHon'A : Hon (s₀ + n + 1) ⊆ honestActiveAt S Sched (s₀ + n + 1) := by
        intro u hu
        unfold honestActiveAt activeAt
        rw [Finset.mem_sdiff]
        exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHonN' u hu t h1 h2).1),
          (hHonN' u hu _ hd2 le_rfl).2⟩
      have hUpdN : Hon (s₀ + n) ⊆ updaterAt S Sched (s₀ + n) := by
        intro u hu
        unfold updaterAt
        rw [Finset.mem_sdiff]
        exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 =>
            (hHonN u hu t (le_trans hdd h1) h2).1),
          (hHonN u hu _ (le_trans hdd hd1) le_rfl).2⟩
      have hSubN : Hon (s₀ + n + 1) ⊆ Hon (s₀ + n) := hHonMono (s₀ + n) (by omega) (by omega)
      have hStepN : ∀ C : Block V, ((fun C => 𝓒 C ∨ ∃ σ, s₀ ≤ σ ∧ σ < s₀ + n ∧
          ∃ v ∈ Hon σ, ∃ C' : Block V,
            (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
            C.AncestorEq C') C ∨ ∃ v ∈ Hon (s₀ + n),
          (stateBefore x (supportCutoff S (s₀ + n + 1) + 1) v).A.saved_confirmation (s₀ + n) =
            some C) →
          ∀ w ∈ Hon (s₀ + n + 1), StepFrameAt S Sched x C (s₀ + n) w := by
        -- the frame conditions of the step at slot `s₀ + n`
        intro C hC w hw
        rcases hC with (hC | ⟨σ, h1, h2, v, hv', C', hC', hCC'⟩) | ⟨v, hv', hC⟩
        · -- a block of `𝓒`: `B`'s parent or an ancestor of it
          refine stepFrameAt_of_ancestorEq S Sched x B C (s₀ + n) w
            (ancestorEq_trans (hFamPar C hC) hPB) ?_
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · exact hStepB₀ w hw
          · exact hQuiet.2.2.1 (s₀ + n) (by omega) (by omega) w hw
        · -- an ancestor of a member's confirmation of an earlier slot of the window
          exact stepFrameAt_of_ancestorEq S Sched x C' C (s₀ + n) w hCC'
            (hQ4 (s₀ + n) (by omega) (by omega) σ h1 (by omega) v hv' C' hC' w hw)
        · -- a member's confirmation of slot `s₀ + n`
          exact hQ4 (s₀ + n) (by omega) (by omega) (s₀ + n) (by omega) le_rfl v hv' C hC w hw
      have hP1 := lem89s_chain_step_upTo S Sched x GST (s₀ + n) (Hon (s₀ + n)) (Hon (s₀ + n + 1))
        (Hon (s₀ + n)) _ hDiv hMono (hSync.mono (hscm _ _ (by omega)))
        (hCatch.mono (hscm _ _ (by omega))) (hRoots.mono (hscm _ _ (by omega))) hParent
        hOwner hGSTn hHonA hHon'A
        hUpdN hSubN (hCommittees (s₀ + n) (by omega) (by omega))
        (hCommittees (s₀ + n + 1) (by omega) (by omega)) hI (fun u hu => Or.inl (hSubN hu)) hL
        (fun C hC v hv C' hC' => (hI C hC).2.2 v hv C' hC') hStepN
      -- the lock invariant at every member of `Hon (s₀ + n + 1)`, its own confirmation joining
      -- the family since it is a member of `Hon (s₀ + n)`
      have hP2 : ∀ u ∈ Hon (s₀ + n + 1), LiveLocksOnFamilyAt S Sched x (fun C => (𝓒 C ∨
          ∃ σ, s₀ ≤ σ ∧ σ < s₀ + n ∧ ∃ v ∈ Hon σ, ∃ C' : Block V,
            (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
            C.AncestorEq C') ∨ ∃ v ∈ Hon (s₀ + n), ∃ C' : Block V,
          (stateBefore x (supportCutoff S (s₀ + n + 1) + 1) v).A.saved_confirmation (s₀ + n) =
            some C' ∧ C.AncestorEq C') (s₀ + n + 1) u :=
        fun u hu => liveLocksOnFamilyAt_step S Sched x _ _ (s₀ + n) u hDiv
          (fun t h1 h2 => hHonN' u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega)) (fun C hC => Or.inl hC)
          (fun C hC => Or.inr ⟨u, hSubN hu, C, hC, ancestorEq_refl C⟩) (hL u (hSubN hu))
      have hP := And.intro hP1 hP2
      · refine ⟨?_, ?_⟩
        · intro C hC
          refine hP.1 C ?_
          rcases hC with hC | ⟨σ, h1, h2, v, hv', C', hC', hCC'⟩
          · exact Or.inl (Or.inl hC)
          · rcases Nat.lt_or_ge σ (s₀ + n) with hlt | hge
            · exact Or.inl (Or.inr ⟨σ, h1, hlt, v, hv', C', hC', hCC'⟩)
            · obtain rfl : σ = s₀ + n := by omega
              exact Or.inr ⟨v, hv', C', hC', hCC'⟩
        · intro u hu A' hR' e he hl
          obtain ⟨D, hD, heD⟩ := hP.2 u hu A' hR' e he hl
          refine ⟨D, ?_, heD⟩
          rcases hD with (hD | ⟨σ, h1, h2, v, hv', C', hC', hDC'⟩) | ⟨v, hv', C', hC', hDC'⟩
          · exact Or.inl hD
          · exact Or.inr ⟨σ, h1, by omega, v, hv', C', hC', hDC'⟩
          · exact Or.inr ⟨s₀ + n, by omega, by omega, v, hv', C', hC', hDC'⟩
  have hFinal := hIter (s₂ + 1 - s₀) (by omega)
  rw [show s₀ + (s₂ + 1 - s₀) = s₂ + 1 by omega] at hFinal
  refine ⟨h80a, ?_, h80c, ?_, ?_, ?_⟩
  · rcases h80b with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h3, Hon (s₀ + 1), hQuorum, h2⟩
  · -- every member saves `B` as the confirmation of slot `s`
    intro v hv'
    obtain ⟨A', hA', hsave, -⟩ := hUpd v hv'
    have h1 := hdwm (s₀ + 1) (s₀ + 1 + 1) (by omega)
    have h2 := hdwv (s₀ + 1 + 1)
    have h3 := hc (s₀ + 1 + 1)
    have hva := hHon (s₀ + 1) (by omega) (by omega) v hv' (supportCutoff S (s₀ + 1 + 1))
      (by omega) le_rfl
    have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s₀ + 1 + 1)
      (supportCutoff S (s₀ + 1 + 1)) v hDiv hMono (by omega)
      (fun t h1' h2' => (hHon (s₀ + 1) (by omega) (by omega) v hv' t (by omega) h2').1) hva.2
    obtain ⟨A'', hA'', hsave', -, -, -⟩ :=
      update_state_of_duty S Sched x (s₀ + 1) v hDiv hva hAw
    have hAA : A' = A'' := by
      rw [hA'] at hA''
      injection hA''
    rw [hsave', ← hAA]
    exact hsave
  · -- the chain invariant at slot `s'' − 1`
    intro C hC
    rcases hC with hC | rfl | ⟨σ, h1, h2, v, hv', hC⟩
    · exact hFinal.1 C (Or.inl hC)
    · exact hInv'
    · exact hFinal.1 C (Or.inr ⟨σ, h1, by omega, v, hv', C, hC, ancestorEq_refl C⟩)
  · -- the lock invariant at slot `s'' − 1`
    intro w hw A' hR' e he hl
    obtain ⟨D, hD, heD⟩ := hFinal.2 w hw A' hR' e he hl
    rcases hD with hD | ⟨σ, h1, h2, v, hv', C', hC', hDC'⟩
    · exact ⟨D, Or.inl hD, heD⟩
    · exact ⟨C', Or.inr (Or.inr ⟨σ, h1, by omega, v, hv', hC'⟩), ancestorEq_trans heD hDC'⟩

end GoldilocksCorrectness.Proofs.Executions

