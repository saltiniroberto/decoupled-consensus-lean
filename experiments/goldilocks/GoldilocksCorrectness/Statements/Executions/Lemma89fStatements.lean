module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f

@[expose] public section

/-!
# Lemma 89f: the AC's healing in front

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma89f.lean`:

- `lem89fq_front`, Lemma 89f with two frame hypotheses: from slot `s_w + 2k − 1` on, the chain
  invariant relative to every live honest lock block and every honest root, and the lock invariant
  relative to them, proved.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 89f with the frame conditions of the front.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST ≤ tGAT`; `Hon s₁` is one set
of validators per slot, the set of slot `s₁ + 1` inside that of slot `s₁` for every slot from
`s_w` to before `s'`; every member of the set of a slot `s₁` from `s_w` to `s'` is outside the
adversary set at the support cutoff of slot `s₁ + 1`; every validator outside the adversary set at
a time from `tGAT` to `tAwakeEnd` is awake then; the committee of every slot `s₁` from `s_w + k` to
`s'` has fewer than twice its members in `Hon s₁`; the duty window of slot `s_w` starts at or after
`tGAT`; `s_w + 2k − 1 ≤ s'`; the support cutoff of slot `s' + 1` is at most `tAwakeEnd`; and

1. (`hFrame`) at every slot `s₁` from `s_w + k − 1` to `s' − 1`, for every slot `σ` from
   `s_w + k − 1` to `s₁` and every confirmation `C` of slot `σ` that a member of `Hon (σ + 1)`
   holds right after the support cutoff of slot `σ + 1`, every member `w` of `Hon (s₁ + 1)`
   satisfies `StepFrameAt S Sched x C s₁ w`;
2. (`hRootsOn`) for every member `w` of `Hon s'`, `w`'s fork-choice root before the vote time of
   slot `s' + 1` is an ancestor of, or equal to, the block of a lock entry a member of `Hon s'`
   holds live before that vote time, or a confirmation of slot `s' − 1` that a member of `Hon s'`
   holds right after the support cutoff of slot `s'` —

then `ChainInvFor` holds at slot `s'` at `Hon s'` for the family
`FrontFamily S Sched x (Hon s') s'`, and every member of `Hon s'` satisfies `LiveLocksOnFamilyAt`
for it.

Why: with `b₀ := s_w + 2k − 2`, every lock entry a member of `Hon b₀` holds live before the vote
time of slot `b₀ + 1` is the lock of a slot `σ` from `s_w + k − 1` to `b₀ − 1` (Lemmas 39 and 41)
on the holder's confirmation of slot `σ` or an ancestor of it. At slot `σ + 1` the invariant
relative to its block holds: the members' votes extend it (Lemma 45b, its frame conditions from
`hFrame` at slot `σ`, `GST` before the vote time of slot `σ + 1 − k`), those votes are a
majority of the committee for blocks on its chain, so the live locks the revocation of slot
`σ + 2` leaves are compatible with it (`locks_clause_of_votes`: Lemma 12, then Lemma 5, with the
finalized blocks from `hFrame`), the confirmations of slot `σ + 1` extend it (Lemma 78); Lemma 79's step over the per-slot sets
(`lem79_step_sets`) carries it to slot `b₀`, `hFrame` giving the frames. From slot `b₀` on, the
phase step `lem89s_phase_step` carries the invariant relative to the members' live lock blocks and
their ancestors: the frames from `hFrame` (each lock is on its holder's confirmation of a slot from
`s_w + k − 1`), the lock invariant from Lemma 38, and every live lock block of the next slot on
the chain of this slot's or of a member's new confirmation (`live_lock_entry_source`). At slot
`s'` the roots are in that family by `hRootsOn`; the lock invariant relative to `FrontFamily` is
Lemma 38 again.

The committee majorities are read from slot `s_w + k` on (not from `s_w + k − 1`): the first
counted committee is slot `σ + 1 ≥ s_w + k`'s, at the confirmations of the base. The proof reads no
synchrony of attestations, no unforgeability, no bound on the adversary set and no set of the
validators honest at `tAwakeEnd`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `tGAT`, `tAwakeEnd`: the phase, in which
  every honest validator is awake; `s_w`: a slot whose duty window starts at or after `tGAT`;
  `s'`: the slot of the conclusion; `Hon`: the member sets.

Read aloud: when, from slot `s_w + k − 1` on, the members' frames follow every member's
confirmation, and at slot `s'` every member's root is behind a member's live lock or
confirmation, then at slot `s'` the votes, live locks and confirmations of
the members extend every live lock block and every root of a member, and the live locks their
revocations of slot `s' + 1` leave are on the chain of one of those blocks.



Roots name blocks until `supportCutoff S s'`: the proof's base reads Lemmas 45b, 12 and 78 at a
slot at most `s'`, and its carry and phase step at the slots before `s'`, up to the support cutoff
of slot `s'`. -/
theorem lem89fq_front (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    -- the network is synchronous from `tGAT` on
    (hGST : GST ≤ tGAT)
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    -- every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int))
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    -- the committee majority of every slot the front counts, inside that slot's set
    (hCommittees : ∀ s₁, s_w + S.C.k ≤ s₁ → s₁ ≤ s' →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    -- the duty window of slot `s_w` starts at or after `tGAT`; the slot `s'` is at least
    -- `s_w + 2k − 1`, and the support cutoff of slot `s' + 1` is inside the phase
    (hsw : tGAT ≤ dutyWindowStart S s_w)
    (hs' : s_w + 2 * S.C.k - 1 ≤ s') (hEnd : supportCutoff S (s' + 1) ≤ tAwakeEnd)
    -- the members' frames follow every member's confirmation from slot `s_w + k − 1` on
    (hFrame : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
      ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
        ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C s₁ w)
    -- every member's root at slot `s'` is behind a member's live lock or confirmation
    (hRootsOn : ∀ w ∈ Hon s', ∃ D : Block V,
      ((∃ u ∈ Hon s', ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
          is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
            ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
        ∃ v ∈ Hon s',
          (stateBefore x (supportCutoff S s' + 1) v).A.saved_confirmation (s' - 1) = some D) ∧
      (get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S).AncestorEq D) :
    ChainInvFor S Sched x (Hon s') (FrontFamily S Sched x (Hon s') s') s' ∧
    ∀ u ∈ Hon s', LiveLocksOnFamilyAt S Sched x (FrontFamily S Sched x (Hon s') s') s' u :=
  GoldilocksCorrectness.Proofs.Executions.lem89fq_front S Sched x GST tGAT tAwakeEnd s_w s' Hon
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHonMono hHon hAwake hCommittees hsw
    hs' hEnd hFrame hRootsOn

end GoldilocksCorrectness.Statements.Executions
