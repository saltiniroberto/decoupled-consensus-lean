module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89fStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/Lemma89fStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 89f, the theorem of
the same name of `Record/Restated/Proofs/Executions/Lemma89f.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 89f with the frame conditions of the front.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST ≤ tGAT`; `Hon M s₁` is one set
of validators per slot, the set of slot `s₁ + 1` inside that of slot `s₁` for every slot from
`s_w` to before `s'`; every member of the set of a slot `s₁` from `s_w` to `s'` is outside the
adversary set at the support cutoff of slot `s₁ + 1`; every validator outside the adversary set at
a time from `tGAT` to `tAwakeEnd` is awake then; the committee of every slot `s₁` from `s_w + k` to
`s'` has fewer than twice its members in `Hon M s₁`; the duty window of slot `s_w` starts at or
after `tGAT`; `s_w + 2k − 1 ≤ s'`; the support cutoff of slot `s' + 1` is at most `tAwakeEnd`; and

1. (`hFrame`) at every slot `s₁` from `s_w + k − 1` to `s' − 1`, for every slot `σ` from
   `s_w + k − 1` to `s₁` and every confirmation `C` of slot `σ` that a member of `Hon M (σ + 1)`
   holds right after the support cutoff of slot `σ + 1`, every member `w` of `Hon M (s₁ + 1)`
   satisfies `StepFrameAt M S Sched x C s₁ w`;
2. (`hRootsOn`) for every member `w` of `Hon M s'`, the fork-choice root of the state `w`'s tick to
   the vote time of slot `s' + 1` starts from is an ancestor of, or equal to, the block of a lock
   entry a member of `Hon M s'` holds live in the state its own tick to that vote time starts from,
   or a confirmation of slot `s' − 1` that a member of `Hon M s'` saved at its tick to the support
   cutoff of slot `s'` —

then `ChainInvFor` holds at slot `s'` at `Hon M s'` for the family
`FrontFamily M S Sched x (Hon M s') s'`, and every member of `Hon M s'` satisfies
`LiveLocksOnFamilyAt` for it.

Why: with `b₀ := s_w + 2k − 2`, every lock entry a member of `Hon M b₀` holds live before the vote
time of slot `b₀ + 1` is the lock of a slot `σ` from `s_w + k − 1` to `b₀ − 1` (Lemmas 39 and 41)
on the holder's confirmation of slot `σ` or an ancestor of it. At slot `σ + 1` the invariant
relative to its block holds: the members' votes extend it (Lemma 45b, its frame conditions from
`hFrame` at slot `σ`, `GST` before the vote time of slot `σ + 1 − k`), those votes are a
majority of the committee for blocks on its chain, so the live locks the revocation of slot
`σ + 2` leaves are compatible with it (`locks_clause_of_votes`: Lemma 12, then Lemma 5, with the
finalized blocks from `hFrame`), the confirmations of slot `σ + 1` extend it (Lemma 78); Lemma 79's
step over the per-slot sets (`lem79_step_sets`) carries it to slot `b₀`, `hFrame` giving the frames.
From slot `b₀` on, the phase step `lem89s_phase_step` carries the invariant relative to the members'
live lock blocks and their ancestors: the frames from `hFrame` (each lock is on its holder's
confirmation of a slot from `s_w + k − 1`), the lock invariant from Lemma 38, and every live lock
block of the next slot on the chain of this slot's or of a member's new confirmation
(`live_lock_entry_source`). At slot `s'` the roots are in that family by `hRootsOn`; the lock
invariant relative to `FrontFamily` is Lemma 38 again.

The committee majorities are read from slot `s_w + k` on (not from `s_w + k − 1`): the first
counted committee is slot `σ + 1 ≥ s_w + k`'s, at the confirmations of the base. The proof reads no
synchrony of attestations, no unforgeability, no bound on the adversary set and no set of the
validators honest at `tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `tGAT`, `tAwakeEnd`: the phase, in which
  every honest validator is awake; `s_w`: a slot whose duty window starts at or after `tGAT`;
  `s'`: the slot of the conclusion; `Hon`: the member sets.

Read aloud: when, from slot `s_w + k − 1` on, the members' frames follow every member's
confirmation, and at slot `s'` every member's root is behind a member's live lock or
confirmation, then at slot `s'` the votes, live locks and confirmations of
the members extend every live lock block and every root of a member, and the live locks their
revocations of slot `s' + 1` leave are on the chain of one of those blocks.



Roots name blocks until `M.supportCutoff S.C s'`: the proof's base reads Lemmas 45b, 12 and 78 at a
slot at most `s'`, and its carry and phase step at the slots before `s'`, up to the support cutoff
of slot `s'`. -/
theorem lem89fq_front (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s'))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s'`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    -- the network is synchronous from `tGAT` on
    (hGST : GST ≤ tGAT)
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s_w`
    (hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s_w)
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    -- every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the committee majority of every slot the front counts, inside that slot's set
    (hCommittees : ∀ s₁, s_w + S.C.k ≤ s₁ → s₁ ≤ s' →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    -- the duty window of slot `s_w` starts at or after `tGAT`; the slot `s'` is at least
    -- `s_w + 2k − 1`, and the support cutoff of slot `s' + 1` is inside the phase
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w)
    (hs' : s_w + 2 * S.C.k - 1 ≤ s') (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    -- the members' frames follow every member's confirmation from slot `s_w + k − 1` on
    (hFrame : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
      ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
        (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C →
        ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C s₁ w)
    -- every member's root at slot `s'` is behind a member's live lock or confirmation
    (hRootsOn : ∀ w ∈ Hon s', ∃ D : Block V,
      ((∃ u ∈ Hon s', ∃ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
          M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
            ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
        ∃ v ∈ Hon s',
          (x.tickOutput v (M.supportCutoff S.C s')).savedConfirmation (s' - 1) = some D) ∧
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (s' + 1)))).AncestorEq D) :
    ChainInvFor M S A x (Hon s') (FrontFamily M S A x (Hon s') s') s' ∧
    ∀ u ∈ Hon s', LiveLocksOnFamilyAt M S A x (FrontFamily M S A x (Hon s') s') s' u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89fq_front M F U) S A x R GST tGAT tAwakeEnd
    s_w s' Hon E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST hGSTw hHonMono hHon hAwake hActive hCommittees
    hsw hs' hEnd hFrame hRootsOn

end GoldilocksCorrectness.Record.Statements.Executions

