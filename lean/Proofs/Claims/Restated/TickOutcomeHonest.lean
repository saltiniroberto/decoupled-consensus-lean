import Proofs.Claims.Restated.RunAll

/-!
# A tick outcome for a validator honest up to the tick

The theorem here gives a tick outcome at a tick step for a validator that is not adversarial at any
time up to the tick, a hypothesis that takes the place of monotone corruption.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Restated

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- If no two blocks in play have two ancestors with one root, an honest proposer never already
    holds a block carrying the root it is about to give its own proposal, step `m` is the tick at
    `t`, `t` is a whole multiple of `S.E.Δ`, `q` is awake and not adversarial at `t`, and `q` is
    adversarial at no time up to `t`, then `q`'s tick at `t` has an outcome from the node state it
    reads. -/
theorem tick_outcome_of_tickStepAt_honest (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    -- No two blocks in play (sent, or held by a validator honest through the step) have two
    -- ancestors with one root.
    (hroot : ∀ B C : NamedBlock V,
      (∃ B' : NamedBlock V,
        ((∃ (i : Nat) (sm : SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block B') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            B' ∈ x[i][v].st.st.bodies)) ∧
        NamedBlock.Preceq B B') →
      (∃ C' : NamedBlock V,
        ((∃ (i : Nat) (sm : SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block C') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            C' ∈ x[i][v].st.st.bodies)) ∧
        NamedBlock.Preceq C C') →
      ∀ A D : NamedBlock V,
        (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
        (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D)
    -- An honest proposer never already holds a block carrying the root it is about to give its own
    -- proposal.
    (hnew : ∀ (k τ : Nat) (s : Slot), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) = M.proposal_time S.E s →
      (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
      ∀ B ∈ x[k][S.E.proposer s].st.st.bodies, B.root ≠ (S.node (S.E.proposer s)).new_root s)
    {m : Nat} {t : Int} {q : V}
    (hm : Restated.tickStepAt M x m t)
    (hΔ : t % S.E.Δ = 0)
    -- `q` is awake and not held by the adversary at `t`.
    (hq : q ∈ Sched.awake t \ Sched.adv t)
    -- `q` is not held by the adversary at any time up to `t`.
    (hh : ∀ t' ≤ t, q ∉ Sched.adv t') :
    ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[m] q) t ⇢ out := by
  obtain ⟨τ, hl, rfl⟩ := hm
  exact facts.ndRun.tick_outcome_sts S Sched x hroot hnew m τ q hl hΔ hq hh

end DecoupledConsensusModel.Sts.Restated
