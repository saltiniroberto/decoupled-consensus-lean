module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FrameShape
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# FrameShapeStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/FrameShapeStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 59, 60 and 61, the
vote, the confirmation and the attestation over a frame shape. Each is the theorem of the same name
of `Record/Restated/Proofs/Executions/FrameShape.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor CountedVotes FrameShape VoterTreeAt)
open GoldilocksCorrectness.Statements.Executions (acObject)

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

/-! ## Lemma 59 -/

/-- **Lemma 59, the next slot's honest vote names the honest proposal, over a frame shape.** Under
the hypotheses of Lemma 24 (`lem24_goldfish_vote_names_honest_proposal_composed`) other than those
on the two frames, and: `p`'s frame before the start `t₁` of slot `s + 1` has the root `ρ_p` and
`head_height_floor` (the least chain-state height a viable block may have) equal to `φ`, and `w`'s frame before the vote time `t₃` of slot `s + 1` has the root `ρ_w` and the same
`head_height_floor` equal to `φ`; some block of `p`'s tree that is `X` or a descendant of `X`, and `ρ_p` or a descendant of
`ρ_p`, has a chain-state height at least `φ`; `ρ_w` is `B` or an ancestor of `B`; and `B`'s
chain-state height is at least `φ` — then `w`'s vote names `B`.

Why: each finalized block is its frame's root or an ancestor of it (Lemma 46); Lemma 56 makes the
block of `p`'s tree a viable head of `p`'s frame and `B` viable at `w`, whose tree holds `B`
(Lemmas 22a and 22), with the chain state `B`'s own (Lemma 11); the two `head_height_floor` values are `φ`. Lemma 24
concludes.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`: their common `head_height_floor`.

Read aloud: the two frames have roots `ρ_p`, `ρ_w` and one `head_height_floor` value `φ`; some accepted block of `p`
on `ρ_p`'s chain descending from `X` reaches `head_height_floor`; `w`'s root is on `B`'s chain; and `B`
reaches `head_height_floor` — then `w`'s vote names `B`.



Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and Lemma 24, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`. -/
theorem lem59_goldfish_vote_names_honest_proposal_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and the same `head_height_floor` value `φ`
    (hShapeW : FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ)
    -- some accepted block of `p` on `ρ_p`'s chain, `X` or a descendant of `X`, reaches `head_height_floor`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- `w`'s root is `B` or an ancestor of `B`
    (hRootW : ρ_w.AncestorEq B)
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B`'s chain-state height reaches `head_height_floor`
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h) :
    vote.head = B.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59_goldfish_vote_names_honest_proposal_frame M F U)
    S A x R GST s Hs H X B p w vote ρ_p ρ_w φ E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST
    hHs hVoters hHold tStart htStart hp hHoldP hw hPropose hSend hOnly hRootNew hShapeP hShapeW hHeadP hApX hRootW hLocksW
    hBHeight

/-! ## Lemma 60 -/

/-- **Lemma 60, the confirmation update makes a voter-majority block fast and locks it, over a
root.** Under the hypotheses of Lemma 29
(`lem29_update_confirmation_fast_locks_voter_majority_block`) with "`v`'s finalized block before
the support cutoff `t₂` of slot `s + 1` is `B` or an ancestor of `B`" replaced by "the root of
`v`'s fork choice before `t₂` is `B` or an ancestor of `B`", `v`'s node state before `t₂ + 1` has
`B` among its fast blocks and the lock entry on `B` with the deadline
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`.

Why: the finalized block is the root of the fork choice or an ancestor of it (Lemma 46); Lemma 29
concludes.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: when the root of `v`'s fork choice is `B` or an ancestor of `B`, Lemma 29's conclusion
holds.



Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: Lemma 29, which the proof calls, takes blocks as
held up to the support cutoff of slot `s`. -/
theorem lem60_update_confirmation_fast_locks_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
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
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- the root of `v`'s fork choice before `t₂` is `B` or an ancestor of `B`
    (hRootV : (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq B) :
    B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem60_update_confirmation_fast_locks_frame M F U)
    S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hHalf hBne
    hv hRootV

/-! ## Lemma 61 -/

/-- **Kit theorem of Lemma 61, Lemma 55's frame hypotheses from a frame shape.** When `v`'s frame
before the support cutoff `t₂` of slot `s + 1` has the root `ρ` and `head_height_floor` equal to `φ`, `ρ` is `B` or an
ancestor of `B`, `B`'s chain-state height `H` is at least `φ`, `B` is in `v`'s tree, and `v`'s cache
`h_j` is less than `H`, or `v`'s record holds no lock at `H`, or it locks the root `T` of `B`'s
`T_h` at `H`: then `B` is in `v`'s viable tree, and `v`'s record holds no lock at `H`, or the lock
`T` with every attestation it sent at `H` naming `T`.

Why: `B` is its own viable head (Lemma 56, with Lemma 46 and Lemma 11); a cache `h_j` less than
`H` leaves no lock at `H`, and a lock at `H` has every attestation sent at `H` name it (Lemma 57).


The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the update's;
- `B`: the block; `v`: the validator; `ρ`: the root of `v`'s fork choice; `φ`: its `head_height_floor`.

Read aloud: the frame at `v` has its root on `B`'s chain and its `head_height_floor` at most `B`'s height, and
`v` holds no lock at `B`'s height on another block — then Lemma 55's viable-tree and record
hypotheses hold.

 -/
theorem lem61_frame_hypotheses (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    -- `v`'s frame before `t₂` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape M (x.stateBefore (M.supportCutoff S.C (s + 1)) v) ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `t₂`
    (hBin : B ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).tree)
    -- `v`'s cache `h_j` is less than `B`'s height, or `v`'s record holds no lock at that height,
    -- or it locks `B`'s `T_h` at that height
    (hLockBox : (x.stateBefore (M.supportCutoff S.C (s + 1)) v).justifiedHeight <
        (M.chainStateOf S.C B).h ∨
      (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
        (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).tree ∧
      ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem61_frame_hypotheses M F) S A x R E s B v ρ φ
    hShape hRootV hBHeight hBin hLockBox

/-- **Lemma 61, every honest validator with the honest proposal as its source attests for its
height, over a frame shape.** Write `s` for the first slot of round `r`, `a_r` for its action time,
which is the support cutoff of slot `s + 1`, `H` for the height of `B`'s chain state and `T` for the
root of its `T_h`. Under the hypotheses of Lemma 55 (`lem55_honest_validator_attests_for_height`)
with its viable-tree and record hypotheses replaced by: `v`'s frame before `a_r` has the root `ρ`
and `head_height_floor` equal to `φ`; `ρ` is `B` or an ancestor of `B`; `H` is at least `φ`; `B` is in `v`'s tree
before `a_r`; and `v`'s cache `h_j` is less than `H`, or `v`'s record holds no lock at `H`, or it
locks `T` at `H` — then `v`
put at its tick at `a_r` an attestation of `v` at `H` naming `T` on the wire, or its record before
`a_r` already holds one sent at `H` naming `T`.

Why: the kit theorem `lem61_frame_hypotheses` gives Lemma 55's viable-tree and record hypotheses;
Lemma 55 concludes.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the support cutoff
  of slot `s + 1`;
- `ρ`: the root of `v`'s fork choice; `φ`: its `head_height_floor`.

Read aloud: the frame at `v` has root `ρ`, on `B`'s chain, and `head_height_floor` at most `B`'s height; the
cache `h_j` is less than `B`'s height, or there is no lock at that height, or the lock there is
`B`'s `T_h` — then Lemma 55's
conclusion.

 -/
theorem lem61_honest_validator_attests_frame (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `s` is the first slot of round `r`, so the action time of `r` is the support cutoff
    -- of slot `s + 1`
    (hs : s = r * S.C.R)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to `a_r`
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    -- `v`'s update of slot `s + 1` at `a_r` leaves `n'`
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    -- `n'` saves `B` as the confirmation of slot `s`
    (hSaved : M.savedConfirmation n' s = some B)
    -- `B` is a fast block of `n'`
    (hFast : B ∈ M.fastBlocks n')
    -- every lock entry of `n'` live at `a_r` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `v`'s frame before `a_r` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `a_r`
    (hBin : B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree)
    -- `v`'s cache `h_j` is less than `H`, or `v`'s record holds no lock at `H`, or it locks `T`
    -- at `H`
    (hLockBox : (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight <
        (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) :
    (∃ (i : ℕ) (a : Attestation V),
      x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = v ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h = (M.chainStateOf S.C B).h ∧ b.T = (M.chainStateOf S.C B).T_h.root) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem61_honest_validator_attests_frame M F U) S
    A x R r s B v ρ φ E hs hv n' sent hUpdate hAwake hSaved hFast hLocks hShape hRootV hBHeight
    hBin hLockBox

end GoldilocksCorrectness.Record.Statements.Executions

