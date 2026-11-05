module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma21
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma36a
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# EligibleBlockVoteStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/EligibleBlockVoteStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 21, the next
slot's honest Goldfish vote extends an eligible block, and Lemma 36a, a confirmed block is extended
by the next slot's honest votes. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma21.lean` or
`Record/Restated/Proofs/Executions/Lemma36a.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor CountedVotesAt EarlySupporterOf
  VoterTree VoterTreeAt)
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated VoterTreeAt)

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

/-- **Lemma 21, the next slot's honest vote extends a block an honest validator finds eligible.**
In an execution where every time is reached, corruption is permanent, blocks and Goldfish votes
are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block
reaches a validator only once it holds the parent: if `GST` is at most the support cutoff of slot
`s`; `v` is awake and honest at every time from the vote time `t₃` of slot `s + 1` to the support
cutoff `t₂` of slot `s + 1`; `w` is awake and honest at every time from the support cutoff of slot
`s` to the view freeze of slot `s`; on `v`'s node state before `t₂`, each
member of `Sup` has exactly one slot-`s` vote, resolved strictly before `S.C.t_ s + 2 · S.C.Δ`,
whose head is the root of a block of `v`'s frame tree that is `B` or a descendant of `B`
(`EarlySupporterOf`), and the validators with a slot-`s` vote in `v`'s pool are fewer than twice
`Sup`; on `w`'s node state before `t₃`, the root of the fork choice is compatible with `B` (F2),
when that root is `B` or an ancestor of `B` some block of `w`'s voter tree for slot `s + 1` that is
`B` or a descendant of `B` is a viable head (F3), and the block of every lock entry live at `t₃`
that `w`'s revocation of slot `s + 1` leaves is compatible with `B` (G4's condition); and `w` put
the Goldfish vote `vote` on the wire at its tick at `t₃` — then `vote`'s head is the root of a block
that is `B` or a descendant of `B`.



Why: `w`'s tick at `t₃` sent `vote`, so its head is the root of the end `H_w` of the Goldfish fork
choice from the anchor of `w`'s revoked AC state (Lemma 14). Each member `u` of `Sup` has its vote
in `v`'s pool before the support cutoff `c` of slot `s`; `v` re-sent it, so it reaches `w` before
the view freeze of slot `s`; `w` holds no second vote of `u` then, since every vote `w` re-sent
before `t₃` reaches `v` before `t₂`, where `u` has one vote; the vote's head reaches `w` before the
view freeze too, so the vote is counted at `w` as `u`'s only vote, a support vote for `B`'s chain.
Every validator with a vote `w` counts has a vote at `v` for the same reason, so `w`'s voters are
fewer than twice `Sup`. The anchor is compatible with `B` (Lemma 6, with the lock condition and
F2) and starts towards `B` (Lemma 7, with F3, the path blocks being ancestors of a supporter's head
stamped before the view freeze), so the fork choice ends at `B` or a descendant of `B` (Lemma 2).
When instead `B` is an ancestor of `w`'s finalized block, `B` is an ancestor of `fc_root` (Lemma
46), of the anchor, and so of `H_w`, which is the anchor or a descendant of it.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block `v` finds eligible;
- `v`: the validator whose confirmation update of slot `s` finds `B` eligible; `w`: the voter of
  slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: if the honest `v`'s state at the support cutoff of slot `s + 1` has a set `Sup` of
early supporters of `B`'s chain with fewer than twice `Sup` voters, `v` is awake and honest from the
duty window's start of slot `s + 1` up to its tick to that cutoff, the honest `w` is active from a time `tStartW`, more than `ΔClockAhead + ΔClockBehind` before the view freeze of slot `s` less `max (3 * Δ S) Δs`, up to its tick to that view freeze, F2 and F3 hold for `B` at `w`, and no live lock `w`'s revocation leaves
conflicts with `B`, then `w`'s vote of slot `s + 1` is for `B` or a descendant of `B`.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 64, which the proof calls with `t_w :=
voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s fork choice. -/
theorem lem21_goldfish_vote_extends_eligible_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`, awake and honest from the duty window's start of slot `s + 1` up to its tick to that
    -- slot's support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `B` is eligible at `v`'s update of slot `s`: each member of `Sup` is an early supporter of
    -- `B`'s chain at `v`, and `v`'s late voters are fewer than twice `Sup`
    (hSup : ∀ u ∈ Sup,
      EarlySupporterOf M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s B u)
    (hEligible :
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
        2 * Sup.card)
    -- the finality-gadget conditions at `w`, on its state before `voteTime S (s + 1)`
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ B.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `B`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ B.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem21_goldfish_vote_extends_eligible_block M F U) S A x R
    GST s Sup B v w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hv tStartW htStartW hw hw₀ hSup
    hEligible hF2 hF3 hLocks hSend

/-- **Lemma 36a, a confirmed block is extended by the next slot's honest votes.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches a
validator only once it holds the parent: if `GST` is at most the support cutoff of slot `s`; `v` is
awake and honest at every time from the vote time `t₃` of slot `s + 1` to the support cutoff `t₂`
of slot `s + 1`; `w` is active from a time `tStartW`, more than `ΔClockAhead + ΔClockBehind` before the view freeze of slot `s` less `max (3 * Δ S) Δs`, up to its tick to that view freeze; `v`'s confirmation update of slot `s + 1`, on its node state before `t₂` with the
expired lock entries removed, leaves `n'`, and `n'` saves `C'` as the confirmation of slot `s`;
on `w`'s node state before `t₃`, the root of the fork choice is compatible with `C'` (F2), when that
root is `C'` or an ancestor of `C'` some block of `w`'s voter tree for slot `s + 1` that is `C'` or
a descendant of `C'` is a viable head (F3), and the block of every lock entry live at `t₃` that
`w`'s revocation of slot `s + 1` leaves is compatible with `C'`; and `w` put the Goldfish vote
`vote` on the wire at its tick at `t₃` — then `vote`'s head is the root of a block that is `C'` or a
descendant of `C'`.

Why: Lemma 36, at the block `C'` itself, gives a set `Sup` of early supporters of `C'` at `v`, with
the validators holding a slot-`s` vote in `v`'s pool before `t₂` fewer than twice `Sup`; its
hypothesis on the pool's stamps holds, every vote in the pool before `t₂` being stamped before
`t₂`. Removing the expired lock entries changes neither the pool nor the stamps, so these are the
hypotheses of Lemma 21 for `B := C'`, which concludes.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot whose confirmation `v`'s
  update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `n'`: the node state
  that update leaves;
- `w`: the voter of slot `s + 1`; `tStartW`: the start of `w`'s window; `vote`: the Goldfish vote `w` sent at the vote time of slot
  `s + 1`.

Read aloud: if the honest `v`'s confirmation update at the support cutoff of slot `s + 1` saves
`C'` as the confirmation of slot `s`, `v` being awake and honest from the duty window's start of
slot `s + 1` up to its tick to that cutoff, then every honest voter `w` of slot `s + 1` that is active from a time more than `ΔClockAhead + ΔClockBehind` before the view freeze of slot `s` less `max (3 * Δ S) Δs` up to its tick to that view freeze, meets F2 and F3 for `C'`, and has no live lock left by its
revocation that conflicts with `C'`, votes for `C'` or a descendant of `C'`.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 21, which the proof calls, takes blocks
as held up to one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem36a_confirmed_block_extended_by_next_honest_votes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (C' : Block V) (v w : V) (n' : M.N)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`, awake and honest from the duty window's start of slot `s + 1` up to its tick to that
    -- slot's support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v`'s update of slot `s + 1`, on its state before the support cutoff with the expired lock
    -- entries removed, leaves `n'`
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    -- `n'` saves `C'` as the confirmation of slot `s`
    (hSaved : n'.savedConfirmation s = some C')
    -- the finality-gadget conditions at `w`, on its state before `voteTime S (s + 1)`
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible C' = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq C' →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          C'.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `C'`
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible C' = true)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ C'.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem36a_confirmed_block_extended_by_next_honest_votes M F U)
    S A x R GST s C' v w n' vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hv tStartW htStartW hw hw₀
    hUpdate hSaved hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Statements.Executions

