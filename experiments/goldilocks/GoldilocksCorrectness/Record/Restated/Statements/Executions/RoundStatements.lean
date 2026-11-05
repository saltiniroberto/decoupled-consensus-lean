module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBoxes
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.BoxStatements
public import GoldilocksCorrectness.Statements.Executions.BoxStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# RoundStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/RoundStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 80 over frame shapes and
over per-slot member sets, what each box supplies to Lemma 80, and the box corollaries of both
forms, read with the greatest chain-state height `hMax M S.C n` of the node's tree in place of the
cache `h_max`. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma80.lean` or
`Record/Restated/Proofs/Executions/RoundBoxes.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt)
open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes FrameShape
  ProposalCountedVotes)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt hMax)
open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxThree BoxTwo CountedVotes
  FrameShape ProposalCountedVotes)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## Lemma 80 over per-slot member sets -/

open Classical in
/-- **Lemma 80 over per-slot member sets, with `q`'s fork choice before its proposal.** Write
`s = r · R` for the first slot of round `r`, `B` for the honest proposal of slot `s` by `p`, `H`
for the height of `B`'s chain state and `T` for the root of its `T_h`, `a` for the action time (the
support cutoff of slot `s + 1`), and `s''` for a slot whose start is at least `Δ_F` after `a`
(`hs''`: an attestation sent at `a` is delivered before slot `s''` starts) and whose proposer `q`
puts `B'` on the wire at its start. In an execution with the eight execution assumptions and
attestations delivered within `Δ_F` after `GST`: if the member sets `Hon M s'` shrink from slot to
slot and each member of `Hon M s'` is awake and honest from the duty window's start of slot `s'` to
the support cutoff of slot `s' + 1` (not past the start of slot `s''`); `p` is active from the
recovery delay before the support cutoff of slot `s − 1` to the start of slot `s`; the slot `s − 1` is as Lemma 59 reads it;
the honest voters `Hs s'` of every slot of the round are in `Hon M s'` and outnumber half the voters
its members count; the frames are read at three points — `p`'s before the start of slot `s` (root
`ρp`, `head_height_floor` `φ`), each member's before the vote time of slot `s` (root on `B`'s
parent's chain, `head_height_floor` between `φ` and the height of `B`'s parent) and before `a` (root
on `B`'s chain, `head_height_floor` at most `H`); after `a`, `StepFrameAt` relative to `B` holds at
the members of `Hon M (s' + 1)` for every slot `s'` with `s' + 3 ≤ s''`, and the voter's fork choice
of slot `s'' − 1` at the members of `Hon M (s'' − 1)`; `Q ⊆ Hon M s` is a quorum whose every member,
before `a`, has its cache `h_j` less than `H`, or no lock at `H`, or its lock at `H` on `T`; `q` is
a member of `Hon M (s'' − 1)` whose fork-choice root before the start of slot `s''` is compatible
with `B` and, when it is `B` or an ancestor of `B`, has a viable head on `B`'s chain — then `B'` is
on `B`'s chain, and `B'`'s chain state has a height greater than `H`, or the height `H` with `Q` in
its progress set and `B'`'s slot less than `δt` after `T_h`'s; and when no member of `Q` had sent
anything at `H` before `a`, `B'`'s height is greater than `H`, and its justified block is `B`'s
`T_h` when `B'`'s parent is still at `H`.

Why: the first slot as in Lemma 80, with Lemma 59 for a proposer's `head_height_floor` at most the
voter's and every member's own update making `B` fast; the slot invariant restricted to `B` carried
from each slot's set to the next (Lemma 79 over two sets); the quorum's attestations reach `q`,
awake and honest from the duty window's start of slot `s` as a member of every set; `q`'s walk
passes `B`; Lemma 53 concludes.

This is Lemma 80's form of record over per-slot member sets. It takes `q`'s fork choice before the
start of slot `s''` as the hypothesis `hFrameQ`, since no other hypothesis reads `q`'s fork choice
at that time; at the last slot it takes the voter's fork choice of slot `s'' − 1` (`hStepLast`) and
not the whole of `StepFrameAt`, whose third conjunct (`q`'s finalized block before the support
cutoff of slot `s''`) the proof does not read.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `s''`: the slot of `q`'s proposal;
- `Hon M s'`: the member set of slot `s'`; `Q`: the quorum; `Hs s'`: the honest voters of slot `s'`;
  `H`: the block each voter of slot `s − 1` votes for; `X`: the block those votes extend;
- `B`: the round's proposal; `B'`: `q`'s proposal; `p`, `q`: their proposers;
- `φ`, `ρp`: the `head_height_floor` and the root of `p`'s frame before the start of slot `s`;
  `φw w`, `ρw w`: those of member `w`'s frame before the vote time of slot `s`; `φv v`, `ρv v`:
  those of member `v`'s frame before `a`.

Read aloud: the round theorem asks of each slot's committee majority honesty through its own
slot's update only, reads the frames of the first slot at its three reading points, the chain's
step conditions after the action time, and the next proposer's fork choice at its proposal; then
the next honest proposal is on the round's proposal's chain with the height risen or the progress
quorum on chain.




Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: `round_proposal_extends`, which the proof
calls at the slot `s'' - 2`, takes blocks as held up to the support cutoff of slot `s'' - 1`;
the base and the invariant through the round read earlier. -/
theorem lem80wq_round_height_advances_steps (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape M (x.tickInput w (M.voteTime S.C s)) (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (M.chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (M.chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80wq_round_height_advances_steps M F U Fx) S
    A x R GST r s s'' Hon Q Hs H X B B' p q φ φw φv ρp ρw ρv E hNet hSkew hRedeliver hRoots
    hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGST hGSTF hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold hVotersPrev
    hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hShapeP hShapeW hShapeV hFloorW hFloorV
    hRootW hRootAr hHeadP hStep hStepLast hQ hQuorum hLockBox hselq hq hqWin hFrameQ hPropose'

/-! ## Lemma 80 -/

/-- **Lemma 80, the height advances in a round, over frame shapes.** Write `s = r · R` for the
first slot of round `r`, `B` for the honest proposal of slot `s`, `H` for the height of `B`'s chain
state and `T` for the root of its `T_h`, `a` for the action time of the round (the support cutoff
of slot `s + 1`), and `s''` for a slot whose start is at least `Δ_F` after `a` (`hs''`: an
attestation sent at `a` is delivered before slot `s''` starts) and whose honest proposer `q` puts
`B'` on the wire at its start. In an execution with the eight execution assumptions and attestations
delivered within `Δ_F` after `GST`: if the members of `Hon` are awake and honest from the duty
window's start of slot `s` to the start of slot `s''`; the slot `s − 1` is as Lemma 24 reads it; the
honest voters `Hs s'` of every slot from `s` to `s'' − 1` are members, each voting at its slot, and
outnumber half the voters every member counts; every member's frame over the window has the root
`ρ v t` and `head_height_floor` (the least chain-state height a viable block may have) equal to `φ`, the root being `B`'s parent or an ancestor of it at the vote time of slot
`s`, `B` or an ancestor of `B` at `a`, and compatible with `B` afterwards; some block of `p`'s tree
on `X`'s and its root's chains reaches `head_height_floor`, and `B`'s parent is in `p`'s viable tree;
`Q ⊆ Hon M` is a quorum whose every member, before `a`, has its cache `h_j` less than `H`, or no
lock at `H`, or its lock at `H` on `T` — then `B'` is on `B`'s chain, and `B'`'s chain state has a
height greater than `H`, or the height `H` with `Q` in its progress set and `B'`'s slot less than
`δt` after `T_h`'s; and when no member of `Q` had sent anything at `H` before `a`, `B'`'s height is
greater than `H`, and its justified block is `B`'s `T_h` when `B'`'s parent is still at `H`.

`Hon` is not an arbitrary set: the hypotheses pin it down. Every member is awake and honest from
the duty window of slot `s` to the start of slot `s''`; it contains the honest voters `Hs s'` of
every slot of the round, the quorum `Q`, and the proposers `p` and `q`; the counting, frame and
root conditions hold at every member. The natural choice is the honest validators awake throughout
that window, for which the first, second and fourth requirements hold by construction and the third
becomes "at least two thirds of the validators are honest and awake throughout the window".

Why: every member votes `B` at slot `s` (Lemma 59), confirms it, makes it fast and keeps no lock off
its chain (Lemmas 60, 27, 42); the slot invariant restricted to `B` carries to slot `s'' − 1`
(Lemma 79); every member of `Q` attests for `(H, T)` at `a` or had (Lemma 61), and the attestation
reaches `q`, a member and so awake and honest from the duty window's start of slot `s`, by the
start of slot `s''`: by synchrony when `q` was awake since the send, by the catch-up on `q`'s last
wake otherwise; `q`'s walk passes `B`; Lemma 53 concludes.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `s''`: the slot of `q`'s proposal;
- `Hon`: the members; `Q`: the quorum; `Hs`: the honest voters of each slot; `H`: the block each
  voter of slot `s − 1` votes for; `X`: the block those votes extend;
- `B`: the round's proposal; `B'`: `q`'s proposal; `p`, `q`: their proposers;
- `φ`: the value of `head_height_floor` at the members' frames; `ρ v j`: the root of `v`'s frame at step `j`.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: inside a window where every member's frame has one `head_height_floor` value and a root on `B`'s chain, the
round's honest proposal is voted, confirmed and attested by every member, and the next honest
proposal, at a slot the round's attestations reach in time, is on its chain with the height risen or
the progress quorum on chain.




Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`:
`lem80wq_round_height_advances_steps`, which the proof calls, reads them per tick. -/
theorem lem80_round_height_advances_frame (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (φ : Height) (ρ : V → ℕ → Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart` (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- at every member and every step from its tick to the start of slot `s` to its tick to the
    -- start of slot `s''`, the frame has the root `ρ v j` and `head_height_floor` `φ`
    (hShape : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (ρ v j) φ)
    -- the roots: at the vote time of slot `s` on `B`'s parent's chain, at `a` on `B`'s chain, and
    -- after the vote time of slot `s` compatible with `B`
    (hRootW : ∀ w ∈ Hon, (ρ w (x.tickStep w (M.voteTime S.C s))).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon, (ρ v (x.tickStep v (M.supportCutoff S.C (s + 1)))).AncestorEq B)
    (hRootAfter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (ρ v j).compatible B = true)
    -- some block of `p`'s tree, on `X`'s and `p`'s root's chains, reaches `head_height_floor` `φ`;
    -- and `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (ρ p (x.tickStep p (M.slotStart S.C s))).AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_round_height_advances_frame M F U Fx) S
    A x R GST r s s'' Hon Q Hs H X B B' p q φ ρ E hNet hSkew hRedeliver hRoots hParent hOwner
    E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGSTF hGST hHon hHold42 hHoldF hp tStart htStart hpR hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew
    hHs hVoters hVotersQ hHalf hShape hRootW hRootAr hRootAfter hHeadP hParentIn hQ hQuorum hLockBox
    hselq hq hqWin hHonestQ hPropose'

/-! ## What each box supplies to Lemma 80 -/

/-- **Lemma 80's frame, root and record hypotheses in box 1.** When every member of `Hon` is in box
1 with `h_max = h₀` at every time from the start of slot `s` to the start of slot `s''`, `p` is a
member, the support cutoff `a` of slot `s + 1` is in that window, and `p`'s proposal `B` has its
parent in `p`'s viable tree: every member's frame over the window has the root `F` and `head_height_floor` equal to
`h₀ − 1`, the finalized-block conditions and `p`'s block reaching `head_height_floor` are passed on as Lemma
80's root conditions and `hHeadP`, and every member's cache `h_j` before `a` is less than `B`'s
height.

Why: box 1 has the root `F` and `head_height_floor` equal to `h_max − 1` (Lemma 56); `B`'s height is at least
`head_height_floor` at `p`, equal to `h₀ − 1` (`proposal_viable`), and `h_j + 1 < h_max = h₀`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the round's first slot; `s''`:
  the end of the window; `Hon`: the members; `X`: the block `p`'s block extends; `B`: the
  proposal; `p`: its proposer; `h₀`: the common `h_max`.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: in box 1 with one `h_max` the round theorem's frame conditions reduce to the box over
the window and the finalized blocks' positions on the proposal's chain, and the record hypothesis
is free.

 -/
theorem lem80_boxOne_hypotheses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- every member is in box 1 with greatest chain-state height `h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxOne M S.C (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at `a`, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    (hp : p ∈ Hon)
    -- `a` is in the window
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀ − 1`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ - 1 ≤ (M.chainStateOf S.C W).h)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, `B`'s parent in its viable tree
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree) :
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (x.st j v).finalized (h₀ - 1)) ∧
    (∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true) ∧
    (∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ - 1 ≤ (M.chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight <
        (M.chainStateOf S.C B).h) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_boxOne_hypotheses M F U) S A x R E hSkew s s'' Hon X B p
    h₀ hHon hBox hFw hFar hFafter hp hs'' hHeadP hPropose hParentIn

/-- **Lemma 80's frame, root and record hypotheses in box 2.** When every member of `Hon` is in box
2 with the justified block `J₀ ≠ genesis` at every time from the start of slot `s` to the start of
slot `s''`, `p` is a member, the support cutoff `a` of slot `s + 1` is in that window, `p`'s
proposal `B` has its parent in `p`'s viable tree, and every member of `Q ⊆ Hon M` has its lock at
`h_max − 1` before `a`, when set, on `J₀`: write `h₀` for `p`'s `h_max` before the start of slot
`s`; then every member's frame over the window has the root `J₀` and `head_height_floor` equal to `h₀ − 1`; `J₀` is an
ancestor of `B`'s parent, of `B`, and compatible with `B`; `p`'s block reaching `head_height_floor` is passed
on; and every member of `Q` before `a` has its cache `h_j` less than `B`'s height `H`, or no lock
at `H`, or its lock at `H` on the root of `B`'s `T_h`.

Why: box 2 has the root `J₀` and `head_height_floor` equal to `h_max − 1 = h_j`, and every `h_j` is `J₀`'s height
(Lemma 57), so every `head_height_floor` value is `h₀ − 1`; `B`'s parent is in the viable tree, whose blocks descend
from the root `J₀`; when `H = h_j = h_max − 1`, a lock at `H` is on `J₀`, which is `B`'s `T_h`
(`entry_block_of_boxTwo`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the round's first slot; `s''`:
  the end of the window; `Hon`: the members; `Q`: the quorum; `X`: the block `p`'s block extends;
  `B`: the proposal; `J₀`: the justified block; `p`: the proposer.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: in box 2 the root condition is free, the `head_height_floor` values agree because every member's `h_max`
is one more than `J₀`'s height, and the lock, when set at `h_max − 1`, is on `J₀`, which is `B`'s
`T_h` when `B` is at `h_max − 1`.

 -/
theorem lem80_boxTwo_hypotheses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (Hon Q : Finset V) (X B J₀ : Block V)
      (p : V)
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- every member is in box 2 with the justified block `J₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxTwo M S.C (x.st j v) J₀)
    -- `J₀` is not the genesis block
    (hJ₀ : J₀ ≠ Block.genesis)
    (hp : p ∈ Hon)
    -- `a` is in the window
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s greatest chain-state
    -- height minus one
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, `B`'s parent in its viable tree
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    (hQ : Q ⊆ Hon)
    -- every member of `Q` has its lock at the greatest chain-state height minus one before `a`,
    -- when set, on `J₀`
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock
        (hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) - 1) = some T' → T' = J₀.root)
            :
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1)) ∧
    J₀.AncestorEq B.parent ∧ J₀.AncestorEq B ∧ J₀.compatible B = true ∧
    (∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h) ∧
    (∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_boxTwo_hypotheses M F U) S A x R E hSkew s s'' Hon Q X B
    J₀ p hHon hBox hJ₀ hp hs'' hHeadP hPropose hParentIn hQ hLockJ₀

/-- **Lemma 80's frame, root and record hypotheses in box 3.** When every member of `Hon` is in box
3 with `h_max = h₀` at every time from the start of slot `s` to the start of slot `s''`, `p` is a
member, the support cutoff `a` of slot `s + 1` is in that window, and `p`'s proposal `B` has its
parent in `p`'s viable tree: every member's frame over the window has the root `F` and `head_height_floor` equal to
`h₀`, the finalized-block conditions and `p`'s block reaching `head_height_floor` are passed on as Lemma 80's
root conditions and `hHeadP`, and every member's cache `h_j` before `a` is less than `B`'s height.

Why: box 3 has `h_max = h_j + 1`, the root `F` and `head_height_floor` equal to `h_max` (Lemma 56); `B`'s height is at
least `head_height_floor` at `p`, equal to `h₀` (`proposal_viable`), so `h_j = h₀ − 1` is less than it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the round's first slot; `s''`:
  the end of the window; `Hon`: the members; `X`: the block `p`'s block extends; `B`: the
  proposal; `p`: its proposer; `h₀`: the common `h_max`.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: box 3 is box 1 with `head_height_floor` equal to `h_max`.

 -/
theorem lem80_boxThree_hypotheses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- every member is in box 3 with greatest chain-state height `h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxThree M (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at `a`, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    (hp : p ∈ Hon)
    -- `a` is in the window
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ ≤ (M.chainStateOf S.C W).h)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, `B`'s parent in its viable tree
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree) :
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (x.st j v).finalized h₀) ∧
    (∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true) ∧
    (∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ ≤ (M.chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight <
        (M.chainStateOf S.C B).h) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_boxThree_hypotheses M F U) S A x R E hSkew s s'' Hon X B
    p h₀ hHon hBox hFw hFar hFafter hp hs'' hHeadP hPropose hParentIn

/-! ## Lemma 80 in the three boxes -/

/-- **Lemma 80 in box 1.** Lemma 80's conclusion under Lemma 80's hypotheses with its frame, root
and record hypotheses replaced by box 1's: every member in box 1 with `h_max = h₀` over the window,
the finalized blocks on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain at the
action time, compatible with `B` afterwards, and some block of `p`'s tree on `X`'s and `p`'s
finalized block's chains reaching `h₀ − 1`.

Why: `lem80_boxOne_hypotheses` gives Lemma 80's frame, root and record hypotheses with the roots
`F` and `head_height_floor` equal to `h₀ − 1`; Lemma 80 concludes.

The variables: those of Lemma 80, with `h₀` the common `h_max` in place of the roots and `head_height_floor`.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the box and the finalized
blocks over the steps from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single
reads at the states its ticks to the vote time of slot `s` and to the support cutoff of slot `s + 1` start from;
each member ticks to the start of slot `s''`, active up to that tick from the trace's start or from its own tick
to a clock value at most `duty_window_start S.C s`; the proposer from its own tick to a clock value at most
`tStart`.

Read aloud: in box 1 the round raises the height or puts the progress quorum on chain.




Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`: the proof reads
Lemma 80 (`lem80_round_height_advances_frame`) at the same slots, which reads them per tick. -/
theorem lem80_boxOne (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members are active through the attestations' sync delay after the later of the duty window's start
    -- of slot `s` and `GST`, where the attestations' sync fact is read
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`, the proposer's
    -- reader start (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- the proposer ticks to the start of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart`
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- every member is in box 1 with greatest chain-state height `h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxOne M S.C (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀ − 1`; and
    -- `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ - 1 ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_boxOne M F U Fx) S A x R GST r s s'' Hon Q
    Hs H X B B' p q h₀ E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGSTF hGST
    hHon hHoldF hp tStart htStart hpR hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hBox
    hFw hFar hFafter hHeadP hParentIn hQ hQuorum hselq hq hqWin hHonestQ hPropose'

/-- **Lemma 80 in box 2.** Lemma 80's conclusion under Lemma 80's hypotheses with its frame, root
and record hypotheses replaced by box 2's: every member in box 2 with the justified block
`J₀ ≠ genesis` over the window, some block of `p`'s tree on `X`'s and `J₀`'s chains reaching `p`'s
`h_max − 1`, and every member of `Q` with its lock at `h_max − 1` before the action time, when
set, on `J₀`.

Why: `lem80_boxTwo_hypotheses` gives Lemma 80's frame, root and record hypotheses with the root
`J₀` and `head_height_floor` equal to `h_max − 1` of `p`'s state before the start of slot `s`; Lemma 80 concludes.

The variables: those of Lemma 80, with `J₀` the justified block in place of the roots and `head_height_floor`.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the box and the finalized
blocks over the steps from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single
reads at the states its ticks to the vote time of slot `s` and to the support cutoff of slot `s + 1` start from;
each member ticks to the start of slot `s''`, active up to that tick from the trace's start or from its own tick
to a clock value at most `duty_window_start S.C s`; the proposer from its own tick to a clock value at most
`tStart`.

Read aloud: in box 2 the round raises the height or puts the progress quorum on chain.




Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`: the proof reads
Lemma 80 (`lem80_round_height_advances_frame`) at the same slots, which reads them per tick. -/
theorem lem80_boxTwo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' J₀ : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members are active through the attestations' sync delay after the later of the duty window's start
    -- of slot `s` and `GST`, where the attestations' sync fact is read
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`, the proposer's
    -- reader start (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- the proposer ticks to the start of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart`
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- every member is in box 2 with the justified block `J₀`, not the genesis block, over the
    -- window
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxTwo M S.C (x.st j v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s greatest chain-state
    -- height minus one; and `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- every member of `Q` has its lock at the greatest chain-state height minus one before the
    -- action time, when set, on `J₀`
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock
        (hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) - 1) = some T' → T' = J₀.root)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_boxTwo M F U Fx) S A x R GST r s s'' Hon Q
    Hs H X B B' J₀ p q E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGSTF hGST
    hHon hHoldF hp tStart htStart hpR hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hBox
    hJ₀ hHeadP hParentIn hQ hQuorum hLockJ₀ hselq hq hqWin hHonestQ hPropose'

/-- **Lemma 80 in box 3.** Lemma 80's conclusion under Lemma 80's hypotheses with its frame, root
and record hypotheses replaced by box 3's: every member in box 3 with `h_max = h₀` over the window,
the finalized blocks on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain at the
action time, compatible with `B` afterwards, and some block of `p`'s tree on `X`'s and `p`'s
finalized block's chains reaching `h₀`.

Why: `lem80_boxThree_hypotheses` gives Lemma 80's frame, root and record hypotheses with the roots
`F` and `head_height_floor` equal to `h₀`; Lemma 80 concludes.

The variables: those of Lemma 80, with `h₀` the common `h_max` in place of the roots and `head_height_floor`.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the box and the finalized
blocks over the steps from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single
reads at the states its ticks to the vote time of slot `s` and to the support cutoff of slot `s + 1` start from;
each member ticks to the start of slot `s''`, active up to that tick from the trace's start or from its own tick
to a clock value at most `duty_window_start S.C s`; the proposer from its own tick to a clock value at most
`tStart`.

Read aloud: in box 3 the round raises the height or puts the progress quorum on chain.




Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`: the proof reads
Lemma 80 (`lem80_round_height_advances_frame`) at the same slots, which reads them per tick. -/
theorem lem80_boxThree (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members are active through the attestations' sync delay after the later of the duty window's start
    -- of slot `s` and `GST`, where the attestations' sync fact is read
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`, the proposer's
    -- reader start (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- the proposer ticks to the start of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart`
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- every member is in box 3 with greatest chain-state height `h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxThree M (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀`; and
    -- `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80_boxThree M F U Fx) S A x R GST r s s'' Hon
    Q Hs H X B B' p q h₀ E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs''
    hGSTF hGST hHon hHoldF hp tStart htStart hpR hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    hBox hFw hFar hFafter hHeadP hParentIn hQ hQuorum hselq hq hqWin hHonestQ hPropose'

/-! ## `lem80wq_round_height_advances_steps` in the three boxes -/

open Classical in
/-- **`lem80wq_round_height_advances_steps` in box 1.** Its conclusion under its hypotheses with
the frame, root and record hypotheses replaced by box facts at the three reading points of slot
`s`: `p` in box 1 before the start of slot `s`; each member of `Hon M s` before the vote time of
slot `s` in box 1 with `h_max` at least `p`'s and at most `h(B.parent) + 1`, or in box 3 with
`h_max` at least `p`'s minus one and at most `h(B.parent)`; each member before the action time `a`
in box 1 with `h_max` at most `h(B) + 1`, or in box 3 with `h_max` at most `h(B)`; the members'
finalized blocks on `B`'s parent's chain before the vote time and on `B`'s chain before `a`; and
some block of `p`'s tree on `X`'s and `p`'s finalized block's chains reaching `p`'s `h_max − 1`.

Why: in boxes 1 and 3 the root is the finalized block and the `head_height_floor` is `h_max − 1`
and `h_max` (Lemma 56), so the bounds on `h_max` place each member's `head_height_floor` between
`p`'s and the parent's height; every member's cache `h_j` before `a` is less than `B`'s height,
which gives the record hypothesis.

The variables: those of `lem80wq_round_height_advances_steps`, without the roots and the
`head_height_floor` values.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the proposer is in box 1 and each member in box 1 or box 3 with its `h_max`
between the proposer's and the parent's height plus one, the round raises the height or puts the
progress quorum on chain.




Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxOne (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 1 before the start of slot `s`
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C s)))
    -- before the vote time of slot `s`, every member of `Hon s` is in box 1 with greatest
    -- chain-state height at least `p`'s and at most `h(B.parent) + 1`, or in box 3 with greatest
    -- chain-state height at least `p`'s minus one and at most `h(B.parent)`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxOne M S.C (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h + 1) ∨
      (BoxThree M (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) + 1 ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h))
    -- before the action time, every member of `Hon s` is in box 1 with greatest chain-state height
    -- at most `h(B) + 1`, or in box 3 with greatest chain-state height at most `h(B)`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxOne M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h + 1) ∨
      (BoxThree M (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- greatest chain-state height minus one
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧ hMax M S.C
        (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80wq_boxOne M F U Fx) S A x R GST r s s'' Hon
    Q Hs H X B B' p q E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ
    hHalf hBoxP hBoxW hBoxV hFw hFar hHeadP hStep hStepLast hQ hQuorum hselq hq hqWin hFrameQ hPropose'

open Classical in
/-- **`lem80wq_round_height_advances_steps` in box 2.** Its conclusion under its hypotheses with
the frame, root and record hypotheses replaced by box facts at the three reading points of slot
`s`: `J₀ ≠ genesis`; `p` before the start of slot `s`, and each member of `Hon M s` before the vote
time of slot `s` and before the action time `a`, in box 2 with the justified block `J₀`; some block
of `p`'s tree on `X`'s and `J₀`'s chains reaching `p`'s `h_max − 1`; `B`'s parent in `p`'s viable
tree; unforgeability; and fewer than a third of the validators corrupted up to `a`.

Why: in box 2 the root is `J₀` and the `head_height_floor` is `h_max − 1 = h_j`, `J₀`'s height
(Lemma 57), the same at every state read; it is at most the parent's height (the parent is a viable
head at `p`), and `J₀` is an ancestor of the parent (the root of `p`'s viable tree); when `B`'s
height is `h_max − 1`, a lock at it is on `J₀` (one justification per height,
`lockBox_of_one_justification`), which is `B`'s `T_h`.

The variables: those of `lem80wq_round_height_advances_steps`, without the roots and the
`head_height_floor` values; `J₀`: the justified block.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the proposer and every member are in box 2 with one justified block, the round
raises the height or puts the progress quorum on chain.




Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxTwo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' J₀ : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `J₀` is not the genesis block; `p` is in box 2 with `J₀` before the start of slot `s`, and
    -- every member of `Hon s` is too before the vote time of slot `s` and before the action time
    (hJ₀ : J₀ ≠ Block.genesis)
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C s)) J₀)
    (hBoxW : ∀ w ∈ Hon s, BoxTwo M S.C (x.tickInput w (M.voteTime S.C s)) J₀)
    (hBoxV : ∀ v ∈ Hon s, BoxTwo M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) J₀)
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s greatest chain-state
    -- height minus one; and `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧ hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤
        (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    -- unforgeability, and fewer than a third of the validators corrupted up to the real time of each member's own tick
    -- to the support cutoff of slot `s + 1` (rule R3;)
    (hAdv : ∀ v ∈ Hon s, A.AdversaryFewerThanThirdUntil x (validator_count V)
        (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80wq_boxTwo M F U Fx) S A x R GST r s s'' Hon
    Q Hs H X B B' J₀ p q E hNet hSkew hRedeliver hRoots hParent E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs''
    hGST hGSTF hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters
    hVotersQ hHalf hJ₀ hBoxP hBoxW hBoxV hHeadP hParentIn hAdv hStep hStepLast hQ hQuorum hselq hq hqWin
    hFrameQ hPropose'

open Classical in
/-- **`lem80wq_round_height_advances_steps` in box 3.** Its conclusion under its hypotheses with
the frame, root and record hypotheses replaced by box facts at the three reading points of slot
`s`: `p` in box 3 before the start of slot `s`; each member of `Hon M s` before the vote time of
slot `s` in box 3 with `h_max` at least `p`'s and at most `h(B.parent)`, or in box 1 with `h_max` at
least `p`'s plus one and at most `h(B.parent) + 1`; each member before the action time `a` in box 3
with `h_max` at most `h(B)`, or in box 1 with `h_max` at most `h(B) + 1`; the members' finalized
blocks on `B`'s parent's chain before the vote time and on `B`'s chain before `a`; and some block of
`p`'s tree on `X`'s and `p`'s finalized block's chains reaching `p`'s `h_max`.

Why: as in box 1, with `p`'s `head_height_floor` `h_max`.

The variables: those of `lem80wq_round_height_advances_steps`, without the roots and the
`head_height_floor` values.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the proposer is in box 3 and each member in box 3 or box 1 with its
`head_height_floor` between the proposer's and the parent's height, the round raises the height or
puts the progress quorum on chain.




Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxThree (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 3 before the start of slot `s`
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C s)))
    -- before the vote time of slot `s`, every member of `Hon s` is in box 3 with greatest
    -- chain-state height at least `p`'s and at most `h(B.parent)`, or in box 1 with greatest
    -- chain-state height at least `p`'s plus one and at most `h(B.parent) + 1`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxThree M (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h) ∨
      (BoxOne M S.C (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) + 1 ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h + 1))
    -- before the action time, every member of `Hon s` is in box 3 with greatest chain-state height
    -- at most `h(B)`, or in box 1 with greatest chain-state height at most `h(B) + 1`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxThree M (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h) ∨
      (BoxOne M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h + 1))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- greatest chain-state height
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧ hMax M S.C
        (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem80wq_boxThree M F U Fx) S A x R GST r s s''
    Hon Q Hs H X B B' p q E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs''
    hGST hGSTF hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters
    hVotersQ hHalf hBoxP hBoxW hBoxV hFw hFar hHeadP hStep hStepLast hQ hQuorum hselq hq hqWin hFrameQ hPropose'

end GoldilocksCorrectness.Record.Statements.Executions

