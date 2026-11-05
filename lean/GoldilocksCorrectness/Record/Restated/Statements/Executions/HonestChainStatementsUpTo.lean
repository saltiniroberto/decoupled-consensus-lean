module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79UpTo
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HonestChainStatementsUpTo, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HonestChainStatementsUpTo.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 78 and Lemma 79,
the step of the slot invariant restricted to a block, with the delivery premises up to a bound. Each
is the theorem of the same name of `Record/Restated/Proofs/Executions/Lemma78UpTo.lean` or
`Lemma79UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (EarlySupporterOf)
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor VoterTreeAt)
open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 78, an honest confirmation update over a voter majority's chain.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the support cutoff `c` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at
the vote time of slot `s`, and holds `H u`, a block that is `B` or a descendant of `B`, in its tree
then; the validators with a slot-`s` vote in `v`'s pool before `c` are fewer than twice `Hs`; `v`
is awake and honest at every time from the duty window's start of slot `s + 1` up to its own tick to `c`; and `v`'s
finalized block before `c` is compatible with `B` — then the confirmation of slot `s` that `v`
holds right after `c`, when it holds one, is `B` or a descendant of `B`.

Why: the state right after `c` holds the confirmation the update of slot `s + 1` saved
(`update_state_of_duty`). When `v`'s finalized block is `B` or an ancestor of `B`, Lemma 12 at `c`
delivers every member's vote to `v`, held early, and Lemma 77 makes the saved confirmation `B` or a
descendant of `B`. When `B` is an ancestor of `v`'s finalized block, the saved confirmation is that
finalized block or a descendant of it (`saved_confirmation_F_ancestorEq`). This is Lemma 27 with
the votes on `B`'s chain in place of votes for `B`, the finalized block compatible with `B` in
place of an ancestor of `B`, without its conditions that `B` is not the genesis block and on the
locks, and concluding on the saved confirmation only.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `B`: the block every vote of `Hs` extends; `v`: the validator running the confirmation update of
  slot `s + 1`.

Read aloud: if every member of `Hs` is a member of the slot-`s` committee, outside the adversary set at
`v`'s tick to the support cutoff of slot `s + 1`, that sent at the vote time of slot `s` a vote for a
block it holds that is `B` or a descendant of `B`, and that is active through the sync delay after Lemma 12's
read time `supportCutoff s − max (2 * Δ S) Δs`; the members of `Hs` are more than half of the validators with a
slot-`s` vote in `v`'s pool before that cutoff; `v` is awake and honest from the duty window's
start of slot `s + 1` up to its own tick to that cutoff; roots name blocks up to `v`'s tick to the support
cutoff of slot `s`; and `v`'s finalized block before the cutoff is compatible with
`B` — then the confirmation of slot `s` that `v` holds right after the cutoff, when it holds one,
is `B` or a descendant of `B`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` its
proof passes the premise to.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `v` by
then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem78_update_confirmation_extends_voter_majority_chain_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member of `Hs` is a member of the slot-`s` committee, outside the adversary set
    -- at `v`'s tick to the support cutoff of slot `s + 1`, that sent its slot-`s` vote for `H u`, a block it holds that is `B`
    -- or a descendant of `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
    -- then `v`'s confirmation of slot `s` right after the cutoff is on `B`'s chain
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ B.AncestorEq (H u))
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the validators with a slot-`s` vote in `v`'s pool before the cutoff are fewer than twice
    -- `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its own tick to the cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v`'s finalized block before the cutoff is compatible with `B`
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    -- then `v`'s confirmation of slot `s` right after the cutoff is on `B`'s chain
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      B.AncestorEq C' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo M F U)
    S A x R GST s Hs H B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hv hF

open Classical in
/-- **Lemma 79, the step of the slot invariant restricted to a block.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after
`GST` (synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s'`; `HonestChainExtends M S Sched x Hon B s'` holds; the members of `Hon` are awake and
honest from the duty window's start of slot `s' + 1` to the support cutoff of slot `s' + 2`; for
each of the slots `s'` and `s' + 1`, every member of `Hs` of that slot is a member of `Hon` and of
that slot's committee that put a vote of that slot on the wire at its tick at that slot's vote time;
at every member `w` voting at slot `s' + 1`, the validators with a vote among those `w` counts are
fewer than twice `Hs s'`, the root of `w`'s fork choice is compatible with `B`, and, when that root
is `B` or an ancestor of `B`, some block of `w`'s voter tree on `B`'s chain is a viable head; and at
every member `v` running the update of slot `s' + 2`, the slot-`(s' + 1)` voters of `v`'s pool
before the support cutoff of slot `s' + 2` are fewer than twice `Hs (s' + 1)`, and `v`'s finalized
block then is compatible with `B` — then `HonestChainExtends M S Sched x Hon B (s' + 1)` holds.



Why: the three clauses at slot `s' + 1` are Lemmas 79a, 79b and 79c; Lemma 79c reads Lemma 79a's
conclusion.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of each slot;
- `B`: the block.

Read aloud: the invariant at slot `s'` gives the invariant at slot `s' + 1`, when the members stay
awake and honest through the next slot, the honest voters of each slot are a majority of the voters
the members count, and the members' finalized blocks and fork-choice roots are compatible with `B`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 79c,
which the proof calls, reads them there; Lemma 79a reads them up to the support cutoff of slot `s'`.

Restated with the delivery premises up to `M.supportCutoff S.C (s' + 1)`: the slot-`(s' + 1)` votes
reach every updater by then (`lem79c_honestChainExtends_confirmations_step_upTo`). -/
theorem lem79_honestChainExtends_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends M S A x Hon B s')
    -- the members of `Hon` are active at every real time from the duty window's start of slot `s' + 1` to its vote
    -- time (Lemma 79a's read), and each runs the update of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the honest voters of slots `s'` and `s' + 1`, members of `Hon` and of the slot's committee
    -- that sent a vote of the slot at its vote time
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the voter bound at every member voting at slot `s' + 1`
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * (Hs s').card)
    -- the voter bound at every member running the update of slot `s' + 2`
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    -- at every member voting at slot `s' + 1`, the root of its fork choice is compatible with `B`
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    -- at every member voting at slot `s' + 1`, when that root is `B` or an ancestor of `B`, a
    -- block of its voter tree on `B`'s chain is a viable head
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W)
    -- the finalized block of every member running the update of slot `s' + 2` is compatible
    -- with `B`
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    -- then the slot invariant restricted to `B` holds at slot `s' + 1`
    HonestChainExtends M S A x Hon B (s' + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem79_honestChainExtends_step_upTo M F U) S A
    x R GST s' Hon Hs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hInv hHon hHonUpd hHonTick hHs hVotersW
    hVotersV hF2 hF3 hFv

end GoldilocksCorrectness.Record.Statements.Executions

