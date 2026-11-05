module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma27
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma29
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma18, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma18.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 18, an honest confirmation update confirms
a block a committee majority voted for. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (committee_card_le_of_majority)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Lemma 18, an honest validator's confirmation update confirms a block a committee majority
voted for early. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/FastConfirmationStatements.lean`. It is Lemmas 27
and 29 with the committee majority, which gives their voter bound because every vote of `v`'s
pool is from the slot-`s` committee, their half condition, and Lemma 27's lock condition through
Lemma 5.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of Lemma 27,
`lock_entries_compatible_of_half` and Lemma 29, which it calls.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: after the support cutoff of slot `s + 1`, `v` has saved `B` as the confirmation of slot
`s`, `B` is a fast block of `v`, `v` holds a lock entry on `B`, and `v`'s latest confirmed block has
advanced to `B`, when the honest voters of `Hs` for `B` are a majority of the slot-`s` committee. -/
theorem lem18_update_confirmation_confirms_majority_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.advance (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
          (x.tickInput v (M.supportCutoff S.C (s + 1))).latestConfirmed (some B) := by
  -- every vote of `v`'s slot-`s` pool at its tick input is from the slot-`s` committee
  have hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E
        (x.tickStep v (M.supportCutoff S.C (s + 1))) v s) hMajority
  have hHalf : (S.P.committee s).card ≤ 2 * Hs.card := committee_card_le_of_majority hMajority
  have hLk := (lock_entries_compatible_of_half M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hOwner hGST hHs hHold hHalf hv hF1
  obtain ⟨hsave, hlatest⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem27_update_confirmation_confirms_voter_majority_block
      M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hBne
      hv hF1 hLk
  obtain ⟨hfast, hlock⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem29_update_confirmation_fast_locks_voter_majority_block
      M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hHalf
      hBne hv hF1
  exact ⟨hsave, hfast, hlock, hlatest⟩

end GoldilocksCorrectness.Record.Proofs.Executions

