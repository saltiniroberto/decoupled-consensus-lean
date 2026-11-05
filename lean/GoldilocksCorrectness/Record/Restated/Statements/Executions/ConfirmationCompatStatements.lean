module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78Compat
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ConfirmationCompatStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/ConfirmationCompatStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 78c, an
honest confirmation update over a majority whose votes are compatible with `B`, and its form with
the delivery premises up to a bound. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma78Compat.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

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

/-- **Lemma 78c, an honest confirmation update over a majority whose votes are compatible with
`B`.** In an execution that reaches every time, with permanent corruption, blocks and Goldfish
votes delivered within `Δ S` from `GST ≤ M.voteTime S.C s`, blocks reaching a validator only after
their parents, nobody voting in an honest validator's name, and roots naming blocks among what
honest validators hold up to the support cutoff of slot `s`: take a set `Hs` of members of slot
`s`'s committee honest at `M.supportCutoff S.C (s + 1)`, each of whose slot-`s` vote for a block
`H u` it holds before the vote time of `s` is on the wire at its tick, `H u` compatible with `B`;
fewer than twice `Hs` validators with a slot-`s` vote in `v`'s pool before
`M.supportCutoff S.C (s + 1)`; `v` ticking to that cutoff and awake and honest from the duty window
of slot `s + 1` (or from its tick to that window's start) up to that tick, its finalized block before it compatible with `B`. Then the confirmation `v`'s update at
that cutoff saves for slot `s`, when there is one, is compatible with `B`.

Why: when `v`'s finalized block is `B` or an ancestor of `B`, every member's vote reaches `v`'s
pool before the support cutoff of `s` as its voter's only vote of the slot, and its block reaches
`v`'s tree, so the frame's block named by the vote's head is `H u`; Lemma 77c. When `B` is an
ancestor of `v`'s finalized block, the saved block descends from that block.

 every hypothesis is read.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is.

Read aloud: when more than half of the counted voters are honest validators whose votes do not
conflict with `B`, and `v`'s finality gadget has not left `B`'s side, no confirmation `v` saves
conflicts with `B`. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    -- the execution reaches every time
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a validator in the adversary set stays in it
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    -- roots name blocks among what honest validators hold up to the real time of `v`'s own tick to the support
    -- cutoff of `s` (:)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    -- the network is synchronous by the vote time of `s`
    -- the window of one delay or one sync delay before the support cutoff of `s` is in the synchronous period
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- each member of `Hs` is a committee member of `s`, outside the adversary set at `v`'s tick to the
    -- cutoff of `s + 1` (where `v` counts the votes), whose
    -- slot-`s` vote for `H u`, a block it holds, is on the wire, `H u` compatible with `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ (H u).compatible B = true)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- fewer than twice `Hs` validators have a slot-`s` vote in `v`'s pool
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    -- `v` ticks to the support cutoff of `s + 1` and is awake and honest from the duty window of
    -- `s + 1`, or from its tick to that window's start, up to that tick
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v`'s finalized block before that cutoff is compatible with `B`
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C'.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem78c_update_confirmation_compatible_of_voter_majority M F U)
    S A x R GST s Hs H B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hv hF

/-- **Lemma 78c with the delivery premises up to the support cutoff of `s`.** Lemma 78c with
`SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at the bound `M.supportCutoff S.C s`, the deadline
of the slot-`s` votes and blocks its proof reads. the catch-up vocabulary stays for phase E's bridge.

Why: Lemma 78c's proof with the deliveries' twins before the bound.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is.

Read aloud: Lemma 78c, with the network synchronous only for what is due by the support cutoff of
slot `s`. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    -- the execution reaches every time
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a validator in the adversary set stays in it
    -- blocks and Goldfish votes due by the support cutoff of `s` are delivered within `Δ S`
    -- after `GST`
    -- roots name blocks among what honest validators hold up to the real time of `v`'s own tick to the support
    -- cutoff of `s` (:)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    -- the network is synchronous by the vote time of `s`
    -- the window of one delay or one sync delay before the support cutoff of `s` is in the synchronous period
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- each member of `Hs` is a committee member of `s`, outside the adversary set at `v`'s tick to the
    -- cutoff of `s + 1` (where `v` counts the votes), whose
    -- slot-`s` vote for `H u`, a block it holds, is on the wire, `H u` compatible with `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ (H u).compatible B = true)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- fewer than twice `Hs` validators have a slot-`s` vote in `v`'s pool
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    -- `v` ticks to the support cutoff of `s + 1` and is awake and honest from the duty window of
    -- `s + 1`, or from its tick to that window's start, up to that tick
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v`'s finalized block before that cutoff is compatible with `B`
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C'.compatible B = true := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem78c_update_confirmation_compatible_of_voter_majority_upTo M F U)
    S A x R GST s Hs H B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hv hF

end GoldilocksCorrectness.Record.Statements.Executions

