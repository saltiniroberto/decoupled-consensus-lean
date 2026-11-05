module
public import GoldilocksCorrectness.Record.TickFacts2
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickLocksGoldilocks
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
import all Goldilocks.AC.Interface
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's tick facts, part 2

`tickFacts2_goldilocks`: the spec's model satisfies `TickFacts2`. At `Model.goldilocks` the tick's
outcomes are those of the spec's duty `Goldilocks.tick`. At the vote time, Lemma 13
(`lem13_tick_revokes_locks`) gives the revocation's answer on the AC state with the expired entries
removed, and the bridge `locksRevoked_of_revoke_locks_eq_ok` gives `LocksRevoked`; at the support
cutoff, Lemma 15 (`lem15_tick_updates_confirmation`) and the bridge
`confirmationUpdated_of_update_confirmation_eq_ok` give `ConfirmationUpdated`. The bridges read
that no two blocks of the frame's tree share a root, a clause of the node invariant
(`nodeInv_frameRoots`). A node not awake since the slot's duty window started fails the tick's
duty test at both times (the window starts before them), and the tick of the available chain then
only deletes the expired lock entries (`ac_on_tick_not_awake`).
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block NamedObject NodeState ACState Frame
  Time duty_window_start record_awake ac_on_tick)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor
  locksRevoked_of_revoke_locks_eq_ok confirmationUpdated_of_update_confirmation_eq_ok)
open GoldilocksCorrectness.Proofs.Routines (DREBPost)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The duty window of the slot of `t` starts before `t` when `t` is that slot's vote time or
support cutoff.

The variables:
- `C`: the configuration; `t`: the time.

Read aloud: the duty window starts before both duty times. -/
theorem duty_window_start_lt_of_dutyTime (C : Config) (t : Time)
    (h : t = C.t_ (C.slot t) + C.Δ ∨ t = C.t_ (C.slot t) + 2 * C.Δ) :
    duty_window_start C (C.slot t) < t := by
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  have hk : (0 : Int) < (C.k : Int) := by
    have := C.k_ge_two
    exact_mod_cast (by omega : 0 < C.k)
  have hm : (0 : Int) < 4 * C.Δ * (C.k : Int) := Int.mul_pos (Int.mul_pos (by decide) hΔ) hk
  have e1 : @Eq Int (duty_window_start C (C.slot t))
      (C.t_ (C.slot t) + C.Δ - 4 * C.Δ * (C.k : Int)) := rfl
  show @LT.lt Int _ (duty_window_start C (C.slot t)) t
  rcases h with h | h
  · have e2 : @Eq Int t (C.t_ (C.slot t) + C.Δ) := h
    omega
  · have e2 : @Eq Int t (C.t_ (C.slot t) + 2 * C.Δ) := h
    omega

omit [Fintype V] in
/-- The tick of the available chain whose two duty tests fail answers the AC state with the expired
lock entries removed.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `A`: the AC state; `Φ`: the frame;
- `t`: the time; `v`: the validator.

Read aloud: with both duty tests failed, the available chain only deletes its expired locks. -/
theorem ac_on_tick_not_awake [Fintype V] [RootOrder] (C : Config) (P : Provisional V)
    (A : ACState V) (Φ : Frame V) (t : Time) (v : V) :
    DREBPost (ac_on_tick C P A Φ t v false false) (fun A₁ => A₁ = expireLocks A t) := by
  simp only [ac_on_tick]
  refine GoldilocksCorrectness.Proofs.Routines.DREBPost.ite (fun hc => ?_) (fun _ => ?_)
  · simp at hc
  · refine GoldilocksCorrectness.Proofs.Routines.DREBPost.ite (fun hc => ?_)
      (fun _ => GoldilocksCorrectness.Proofs.Routines.DREBPost.pure rfl)
    simp at hc

/-- The spec's model satisfies the facts of the tick, part 2.

Read aloud: the spec's tick revokes the locks and updates the confirmation as the record says. -/
theorem tickFacts2_goldilocks : TickFacts2 (Model.goldilocks (V := V)) where
  tick_voteTime_locks := by
    intro _ C P X n t n' sent hRun hInv hVote hAwake
    obtain ⟨A', hA', hE⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks C P X n n' t sent hRun
        hVote hAwake
    exact locksRevoked_of_revoke_locks_eq_ok P n t (C.slot t)
      {e ∈ n.A.lock_entries | t < e.d} A' n'
      (GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hInv.1)
      (fun e he => (Finset.mem_filter.1 he).1) (fun e he hd => Finset.mem_filter.2 ⟨he, hd⟩)
      (fun _ e he => (Finset.mem_filter.1 he).2) hA' hE
  tick_voteTime_locks_of_core := by
    intro _ C P X n t n' sent hRun hInv hVote hAwake
    obtain ⟨A', hA', hE⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks C P X n n' t sent hRun
        hVote hAwake
    exact locksRevoked_of_revoke_locks_eq_ok P n t (C.slot t)
      {e ∈ n.A.lock_entries | t < e.d} A' n'
      (fun B hB B' hB' hr => hInv.1.2.2.2.2.2.2.2.1.1 B
        ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB).1 B'
        ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB').1 hr)
      (fun e he => (Finset.mem_filter.1 he).1) (fun e he hd => Finset.mem_filter.2 ⟨he, hd⟩)
      (fun _ e he => (Finset.mem_filter.1 he).2) hA' hE
  tick_supportCutoff_confirmation := by
    intro _ C P X n t n' sent hRun hInv hCut hAwake
    obtain ⟨A'', hA'', hS, hF, hL, hC⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem15_tick_updates_confirmation C P X n n' t sent
        hRun hCut hAwake
    exact confirmationUpdated_of_update_confirmation_eq_ok C P n t (C.slot t)
      {e ∈ n.A.lock_entries | t < e.d} A'' n'
      (GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hInv.1)
      (fun e => Finset.mem_filter) hA'' hS hF hL hC
  tick_supportCutoff_confirmation_of_core := by
    intro _ C P X n t n' sent hRun hInv hCut hAwake
    obtain ⟨A'', hA'', hS, hF, hL, hC⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem15_tick_updates_confirmation C P X n n' t sent
        hRun hCut hAwake
    exact confirmationUpdated_of_update_confirmation_eq_ok C P n t (C.slot t)
      {e ∈ n.A.lock_entries | t < e.d} A'' n'
      (fun B hB B' hB' hr => hInv.1.2.2.2.2.2.2.2.1.1 B
        ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB).1 B'
        ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB').1 hr)
      (fun e => Finset.mem_filter) hA'' hS hF hL hC
  tick_dutyTime_not_awake := by
    intro _ C P X n t n' sent hRun hDuty hNot
    obtain ⟨A₁, out, out', hrun, hk⟩ :=
      GoldilocksCorrectness.Proofs.Routines.tick_ac_on_tick C P X n n' t sent hRun
    have hb : (record_awake n t).awake_since (duty_window_start C (C.slot t)) = false := by
      cases hb : (record_awake n t).awake_since (duty_window_start C (C.slot t)) with
      | false => rfl
      | true =>
        exact absurd (GoldilocksCorrectness.Proofs.Routines.awakeSince_of_record_awake hb
          (duty_window_start_lt_of_dutyTime C t hDuty)) hNot
    rw [hb] at hrun
    have hA₁ := ac_on_tick_not_awake C P n.A (Goldilocks.fg_to_ac n.S) t n.v out A₁ out' hrun
    subst hA₁
    exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩

end GoldilocksCorrectness.Record
