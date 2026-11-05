module
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.Interface
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 15: the tick at the support cutoff runs the confirmation update

The proof of `lem15_tick_updates_confirmation`, stated in
`GoldilocksCorrectness/Statements/Routines/TickStatements.lean`.

The route: the tick's AC state keeps the four confirmation fields of its tick of the available
chain (`tick_ac_on_tick`; the proposal and the attestation duty keep them, whether or not they
run, trap T9 of the plan); the duty test passes from `hAwake` (`awake_since_record_awake`); at the
support cutoff the tick of the available chain does not revoke (the vote time is not the support
cutoff), and runs the confirmation update on `expireLocks A t` (`ac_on_tick_updates`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREPost)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- At the support cutoff of its slot, when its confirmation test passes, every answer of the tick
of the available chain is the answer of the confirmation update of that slot on
`expireLocks A t`, in the lock entries, the saved confirmations, the fast blocks and the record of
the confirmed tip: the revocation does not run, since the support cutoff is not the vote time.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`: the vote test;
- `A''`: the answer of the confirmation update.

Read aloud: at the support cutoff, the tick of the available chain leaves the update's
confirmation fields. -/
theorem ac_on_tick_updates (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b : Bool) (hCutoff : t = C.t_ (C.slot t) + 2 * C.Δ) :
    DREBPost (ac_on_tick C P A Φ t v b true) (fun A₁ => ∃ A'' : ACState V,
      update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'' ∧
        KeepsConfirmation A'' A₁) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact absurd hCutoff (voteTime_ne_cutoff hc.1)
  · refine DREBPost.ite (fun _ => ?_) (fun hc => ?_)
    · refine DREBPost.bind
        (P := fun A'' => update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'')
        (DREBPost.liftM (fun _ h => h)) (fun A'' hA'' => ?_)
      exact DREBPost.pure ⟨A'', hA'', KeepsConfirmation.refl A''⟩
    · simp only [Bool.and_true, decide_eq_true_eq] at hc
      exact absurd hCutoff hc

/-- **Lemma 15, the tick at the support cutoff runs the confirmation update.** The proof; the
audited statement is in `Statements/Routines/TickStatements.lean`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent;
- `A''`: the answer of the confirmation update. -/
theorem lem15_tick_updates_confirmation (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V))
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hCutoff : t = C.t_ (C.slot t) + 2 * C.Δ)
    (hAwake : ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t)) :
    ∃ A'' : ACState V,
      update_confirmation C P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A'' ∧
        n'.A.saved_confirmation = A''.saved_confirmation ∧ n'.A.fast_blocks = A''.fast_blocks ∧
        n'.A.lock_entries = A''.lock_entries ∧ n'.A.latest_confirmed = A''.latest_confirmed := by
  obtain ⟨τ, hτ, hle⟩ := hAwake
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t sent hRun
  rw [awake_since_record_awake hτ hle] at hrun
  obtain ⟨A'', hA'', hA₁⟩ :=
    ac_on_tick_updates C P n.A (fg_to_ac n.S) t n.v true hCutoff out A₁ out' hrun
  have h := hA₁.trans hk
  exact ⟨A'', hA'', h.2.1, h.2.2.1, h.1, h.2.2.2⟩

end GoldilocksCorrectness.Proofs.Routines
