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
# Lemma 13: the tick at the vote time revokes the locks

The proof of `lem13_tick_revokes_locks`, stated in
`GoldilocksCorrectness/Statements/Routines/TickStatements.lean`.

The route: the tick's AC state keeps the lock entries of its tick of the available chain
(`tick_ac_on_tick`); the duty test passes from `hAwake` (`awake_since_record_awake`); at the vote
time the tick of the available chain revokes the locks on `expireLocks A t`, then runs the
Goldfish vote duty, which keeps the lock entries, and does not run the confirmation update
(`ac_on_tick_revokes`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREPost)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- At the vote time of its slot, when its vote test passes, every answer of the tick of the
available chain has the lock entries of the revocation of that slot on `expireLocks A t`: the
revocation answers some `A'`, the Goldfish vote duty keeps `A'`'s lock entries, and the
confirmation update does not run.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b'`: the confirmation test;
- `A'`: the answer of the revocation.

Read aloud: at the vote time, the tick of the available chain leaves the revocation's locks. -/
theorem ac_on_tick_revokes (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b' : Bool) (hVoteTime : t = C.t_ (C.slot t) + C.Δ) :
    DREBPost (ac_on_tick C P A Φ t v true b') (fun A₁ => ∃ A' : ACState V,
      revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A' ∧
        A₁.lock_entries = A'.lock_entries) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun _ => ?_) (fun hc => ?_)
  · refine DREBPost.bind
      (P := fun A' => revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A')
      (DREBPost.liftM (fun _ h => h)) (fun A' hA' => ?_)
    refine DREBPost.bind (goldfish_vote_keepsConfirmation C P A' Φ t v) (fun A₂ h₂ => ?_)
    refine DREBPost.ite (fun hc => ?_) (fun _ => DREBPost.pure ⟨A', hA', h₂.1⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact absurd hc.1 (voteTime_ne_cutoff hVoteTime)
  · simp only [Bool.and_true, decide_eq_true_eq] at hc
    exact absurd hVoteTime hc

/-- **Lemma 13, the tick at the vote time revokes the locks.** The proof; the audited statement is
in `Statements/Routines/TickStatements.lean`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent;
- `A'`: the answer of the revocation. -/
theorem lem13_tick_revokes_locks (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V))
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hVoteTime : t = C.t_ (C.slot t) + C.Δ)
    (hAwake : ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t)) :
    ∃ A' : ACState V,
      revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
        n'.A.lock_entries = A'.lock_entries := by
  obtain ⟨τ, hτ, hle⟩ := hAwake
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t sent hRun
  rw [awake_since_record_awake hτ hle] at hrun
  obtain ⟨A', hA', hA₁⟩ :=
    ac_on_tick_revokes C P n.A (fg_to_ac n.S) t n.v true hVoteTime out A₁ out' hrun
  exact ⟨A', hA', hk.1.trans hA₁⟩

end GoldilocksCorrectness.Proofs.Routines
